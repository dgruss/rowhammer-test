// Copyright 2015, Google, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Small test program to systematically check through the memory to find bit
// flips by double-sided row hammering.
//
// Compilation instructions:
//   g++ -std=c++11 [filename]
//
// ./double_sided_rowhammer [-t nsecs] [-p percentage]
//
// Hammers for nsecs seconds, acquires the described fraction of memory (0.0
// to 0.9 or so).

#include <asm/unistd.h>
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/kernel-page-flags.h>
#include <map>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/sysinfo.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <vector>

namespace {

// The fraction of physical memory that should be mapped for testing.
double fraction_of_physical_memory = 0.6;

// The time to hammer before aborting. Defaults to one hour.
uint64_t number_of_seconds_to_hammer = 3600;

#define EVICTION_CLASS (13)

// This vector will be filled with all the pages we can get access to for a
// given row size.
std::vector<std::vector<uint8_t*>> pages_per_row;
std::vector<uint8_t*> congruent_pages;
  
// The number of memory reads to try.
#define NUMBER_OF_READS (1024*1024)
uint64_t number_of_reads = NUMBER_OF_READS;

// Obtain the size of the physical memory of the system.
uint64_t GetPhysicalMemorySize() {
  struct sysinfo info;
  sysinfo( &info );
  return (size_t)info.totalram * (size_t)info.mem_unit;
}

int pagemap = -1;

uint64_t GetPageFrameNumber(int pagemap, uint8_t* virtual_address) {
  // Read the entry in the pagemap.
  uint64_t value;
  int got = pread(pagemap, &value, 8,
                  (reinterpret_cast<uintptr_t>(virtual_address) / 0x1000) * 8);
  assert(got == 8);
  uint64_t page_frame_number = value & ((1ULL << 54)-1);
  return page_frame_number;
}

void SetupMapping(uint64_t* mapping_size, void** mapping) {
  *mapping_size = 
    static_cast<uint64_t>((static_cast<double>(GetPhysicalMemorySize()) * 
          fraction_of_physical_memory));

  *mapping = mmap(NULL, *mapping_size, PROT_READ | PROT_WRITE,
      MAP_POPULATE | MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  assert(*mapping != (void*)-1);

  // Initialize the mapping so that the pages are non-empty.
  printf("[!] Initializing large memory mapping ...");
  for (uint64_t index = 0; index < *mapping_size; index += 0x1000) {
    uint64_t* temporary = reinterpret_cast<uint64_t*>(
        static_cast<uint8_t*>(*mapping) + index);
    temporary[0] = index;
  }
  printf("done\n");
}

// Given a physical memory address, this hashes the address and
// returns the number of the cache slice that the address maps to.
//
// This assumes a 2-core Sandy Bridge CPU.
//
// "bad_bit" lets us test whether this hash function is correct.  It
// inverts whether the given bit number is included in the set of
// address bits to hash.
int get_cache_slice(uint64_t phys_addr, int bad_bit) {
  // On a 4-core machine, the CPU's hash function produces a 2-bit
  // cache slice number, where the two bits are defined by "h1" and
  // "h2":
  //
  // h1 function:
  //   static const int bits[] = { 18, 19, 21, 23, 25, 27, 29, 30, 31 };
  // h2 function:
  //   static const int bits[] = { 17, 19, 20, 21, 22, 23, 24, 26, 28, 29, 31 };
  //
  // This hash function is described in the paper "Practical Timing
  // Side Channel Attacks Against Kernel Space ASLR".
  //
  // On a 2-core machine, the CPU's hash function produces a 1-bit
  // cache slice number which appears to be the XOR of h1 and h2.

  // XOR of h1 and h2:
  static const int bits[] = { 17, 18, 20, 22, 24, 25, 26, 27, 28, 30 };

  int count = sizeof(bits) / sizeof(bits[0]);
  int hash = 0;
  for (int i = 0; i < count; i++) {
    hash ^= (phys_addr >> bits[i]) & 1;
  }
  if (bad_bit != -1) {
    hash ^= (phys_addr >> bad_bit) & 1;
  }
  return hash;
}

bool in_same_cache_set(uint64_t phys1, uint64_t phys2, int bad_bit) {
  // For Sandy Bridge, the bottom 17 bits determine the cache set
  // within the cache slice (or the location within a cache line).
  uint64_t mask = ((uint64_t) 1 << 17) - 1;
  return ((phys1 & mask) == (phys2 & mask) &&
          get_cache_slice(phys1, bad_bit) == get_cache_slice(phys2, bad_bit));
}

uint64_t rdtsc() {
  uint64_t a, d;
  asm volatile ("rdtsc" : "=a" (a), "=d" (d));
  a = (d<<32) | a;
  return a;
}

int g_pagemap_fd = -1;

// Extract the physical page number from a Linux /proc/PID/pagemap entry.
uint64_t frame_number_from_pagemap(uint64_t value) {
  return value & ((1ULL << 54) - 1);
}

void init_pagemap() {
  g_pagemap_fd = open("/proc/self/pagemap", O_RDONLY);
  assert(g_pagemap_fd >= 0);
}

uint64_t get_physical_addr(uint64_t virtual_addr) {
  uint64_t value;
  off_t offset = (virtual_addr / 4096) * sizeof(value);
  int got = pread(g_pagemap_fd, &value, sizeof(value), offset);
  assert(got == 8);

  // Check the "page present" flag.
  assert(value & (1ULL << 63));

  uint64_t frame_num = frame_number_from_pagemap(value);
  return (frame_num * 4096) | (virtual_addr & (4095));
}

#define ROW_SIZE (256*1024)
#define ADDR_COUNT (15)

uint64_t HammerAddressesStandard(
    const std::pair<uint64_t, uint64_t>& first_range,
    const std::pair<uint64_t, uint64_t>& second_range,
    uint64_t number_of_reads) {

  volatile uint64_t* f1 = (volatile uint64_t*) second_range.first;
  volatile uint64_t* f0 = (volatile uint64_t*) first_range.first;
  
  uint64_t sum = 0;
  //size_t t = rdtsc();
  while (number_of_reads-- > 0) {
    sum += *(f0);
    sum += *(f1);
    asm volatile("clflush (%0)" : : "r" (f0) : "memory");
    asm volatile("clflush (%0)" : : "r" (f1) : "memory");
  }
  //size_t delta = (rdtsc() - t) / (NUMBER_OF_READS);
  //printf("%zu ",delta);
  return sum;
}

uint64_t hammer_congruent(uint8_t* first, const std::vector<uint8_t*>& pages,size_t poff,uint64_t number_of_reads) {
  volatile uint64_t* f0 = (volatile uint64_t*) first;
  
  //volatile uint64_t* f13 = (volatile uint64_t*) pages.at(12+poff);
  volatile uint64_t* f12 = (volatile uint64_t*) pages.at(11+poff);
  volatile uint64_t* f11 = (volatile uint64_t*) pages.at(10+poff);
  volatile uint64_t* f10 = (volatile uint64_t*) pages.at(9+poff);
  volatile uint64_t* f9 = (volatile uint64_t*) pages.at(8+poff);
  volatile uint64_t* f8 = (volatile uint64_t*) pages.at(7+poff);
  volatile uint64_t* f7 = (volatile uint64_t*) pages.at(6+poff);
  volatile uint64_t* f6 = (volatile uint64_t*) pages.at(5+poff);
  volatile uint64_t* f5 = (volatile uint64_t*) pages.at(4+poff);
  volatile uint64_t* f4 = (volatile uint64_t*) pages.at(3+poff);
  volatile uint64_t* f3 = (volatile uint64_t*) pages.at(2+poff);
  volatile uint64_t* f2 = (volatile uint64_t*) pages.at(1+poff);
  volatile uint64_t* f1 = (volatile uint64_t*) pages.at(0+poff);
  
  uint64_t sum = 0;
  //size_t t = rdtsc();
  while (number_of_reads-- > 0) {
    sum += *(f0);
    sum += *(f1);
    sum += *(f2);
    sum += *(f3);
    sum += *(f4);
    sum += *(f5);
    sum += *(f6);
    sum += *(f7);
    sum += *(f8);
    sum += *(f9);
    sum += *(f10);
    sum += *(f11);
    sum += *(f12);
    //sum += *(f13);
  }
  //size_t delta = (rdtsc() - t) / (NUMBER_OF_READS);
  //printf("%zu ",delta);
  return sum;
}
const uint8_t* flip = 0;

typedef uint64_t(HammerFunction)(
    const std::pair<uint64_t, uint64_t>& first_range,
    const std::pair<uint64_t, uint64_t>& second_range,
    uint64_t number_of_reads);

// A comprehensive test that attempts to hammer adjacent rows for a given 
// assumed row size (and assumptions of sequential physical addresses for 
// various rows.
uint64_t HammerAllReachablePages(uint64_t presumed_row_size, 
    void* memory_mapping, uint64_t memory_mapping_size, HammerFunction* hammer,
    uint64_t number_of_reads) {
  uint64_t total_bitflips = 0;

  pages_per_row.resize(memory_mapping_size / presumed_row_size);
  pagemap = open("/proc/self/pagemap", O_RDONLY);
  assert(pagemap >= 0);
  init_pagemap();

  printf("[!] Identifying rows for accessible pages ... ");
  for (uint64_t offset = 0; offset < memory_mapping_size; offset += 0x1000) {
    uint8_t* virtual_address = static_cast<uint8_t*>(memory_mapping) + offset;
    uint64_t page_frame_number = GetPageFrameNumber(pagemap, virtual_address);
    uint64_t physical_address = page_frame_number * 0x1000;
    uint64_t presumed_row_index = physical_address / presumed_row_size;
    //printf("[!] put va %lx pa %lx into row %ld\n", (uint64_t)virtual_address,
    //    physical_address, presumed_row_index);
    if (presumed_row_index > pages_per_row.size()) {
      pages_per_row.resize(presumed_row_index);
    }
    pages_per_row[presumed_row_index].push_back(virtual_address);
    //printf("[!] done\n");
  }
  printf("Done\n");
  // We should have some pages for most rows now.
  for (uint64_t row_index = 1024; row_index + 2 < pages_per_row.size(); 
      ++row_index) {
    bool cont = false;
    for (int64_t offset = -64; offset < 64; ++offset)
    {
      if (pages_per_row[row_index + offset].size() != 64)
      {
        cont = true;
        printf("[!] Can't hammer row %ld - only got %ld pages\n",
            row_index+offset, pages_per_row[row_index+offset].size());
        break;
      }
    }
    if (cont)
      continue;
    printf("[!] Hammering rows %ld/%ld/%ld of %ld (got %ld/%ld/%ld pages)\n", 
        row_index, row_index+1, row_index+2, pages_per_row.size(), 
        pages_per_row[row_index].size(), pages_per_row[row_index+1].size(), 
        pages_per_row[row_index+2].size());
    // Iterate over all pages we have for the first row.
    for (int frp = 63; frp > 0; --frp) {
      congruent_pages.clear();
      uint8_t* first_row_page = pages_per_row[row_index].at(frp);
      // Iterate over all pages we have for the second row.
      for (uint64_t sec = 0; sec < memory_mapping_size; sec += 0x1000)
      {
        uint64_t phys1 = get_physical_addr((uint64_t)first_row_page);

        uint64_t phys2 = get_physical_addr((uint64_t)memory_mapping + sec);
        if (phys2 / ROW_SIZE == phys1 / ROW_SIZE || !in_same_cache_set(phys1, phys2, -1))
          continue;
        //printf("%zx %zx\n", phys1, phys2);
        uint8_t* second_row_page = (uint8_t*)memory_mapping + sec;
        // Set all the target pages to 0xFF.
        for (int32_t offset = -63; offset < 64; offset += 2)        
        for (uint8_t* target_page : pages_per_row[row_index+offset]) {
            memset(target_page, 0xFF, 0x1000);
        }

        // Now hammer the two pages we care about.
        std::pair<uint64_t, uint64_t> first_page_range(
            reinterpret_cast<uint64_t>(first_row_page), 
            reinterpret_cast<uint64_t>(first_row_page+0x1000));
        std::pair<uint64_t, uint64_t> second_page_range(
            reinterpret_cast<uint64_t>(second_row_page),
            reinterpret_cast<uint64_t>(second_row_page+0x1000));
        hammer(first_page_range, second_page_range, number_of_reads);
        // Now check the target pages.
        uint64_t number_of_bitflips_in_target = 0;
        int32_t offset = -63;
        for (; offset < 64; offset += 2)
        for (const uint8_t* target_page : pages_per_row[row_index+offset]) {
          for (uint32_t index = 0; index < 0x1000; ++index) {
            if (target_page[index] != 0xFF) {
              ++number_of_bitflips_in_target;
              printf("0x%X != 0xFF  ", target_page[index]);
              flip = target_page + index;
              goto done;
            }
          }
        }
done:
        if (number_of_bitflips_in_target > 0) {
          printf("[!] Found %ld flips in row %ld (%lx) when hammering "
              "%lx (%p) and %lx (%p)\n", number_of_bitflips_in_target, row_index+offset,
              GetPageFrameNumber(pagemap, (uint8_t*)flip)*0x1000+(((size_t)flip)%0x1000),
              GetPageFrameNumber(pagemap, first_row_page)*0x1000, first_row_page,
              GetPageFrameNumber(pagemap, second_row_page)*0x1000, second_row_page);
          total_bitflips += number_of_bitflips_in_target;
          congruent_pages.push_back(second_row_page);
          if (congruent_pages.size() > 11) {
            for (size_t poff = 0; poff < congruent_pages.size()-11; ++poff)
            {
              // Set all the target pages to 0xFF.
              for (int32_t offset = -63; offset < 64; offset += 2)        
              for (uint8_t* target_page : pages_per_row[row_index+offset]) {
                  memset(target_page, 0xFF, 0x1000);
              }

              hammer_congruent(first_row_page, congruent_pages, poff, 64*number_of_reads);
              // Now check the target pages.
              uint64_t number_of_bitflips_in_target = 0;
              int32_t offset = -63;
              for (; offset < 64; offset += 2)
              for (const uint8_t* target_page : pages_per_row[row_index+offset]) {
                for (uint32_t index = 0; index < 0x1000; ++index) {
                  if (target_page[index] != 0xFF) {
                    ++number_of_bitflips_in_target;
                    printf("0x%X != 0xFF\n", target_page[index]);
                    flip = target_page + index;
                    goto done2;
                  }
                }
              }
      done2:
              if (number_of_bitflips_in_target > 0) {
                printf("[!] Found %ld flips in row %ld (%lx) when hammering "
                    "%lx (%p) CACHED!!\n", number_of_bitflips_in_target, row_index+offset,
                    GetPageFrameNumber(pagemap, (uint8_t*)flip)*0x1000+(((size_t)flip)%0x1000),
                    GetPageFrameNumber(pagemap, first_row_page)*0x1000, first_row_page);
                total_bitflips += number_of_bitflips_in_target;
              }
            }
          }
        }
      }
    }
  }
  return total_bitflips;
}

void HammerAllReachableRows(HammerFunction* hammer, uint64_t number_of_reads) {
  uint64_t mapping_size;
  void* mapping;
  SetupMapping(&mapping_size, &mapping);

  HammerAllReachablePages(1024*256, mapping, mapping_size,
                          hammer, number_of_reads);
}

void HammeredEnough(int sig) {
  printf("[!] Spent %ld seconds hammering, exiting now.\n",
      number_of_seconds_to_hammer);
  fflush(stdout);
  fflush(stderr);
  exit(0);
}

}  // namespace

int main(int argc, char** argv) {
  // Turn off stdout buffering when it is a pipe.
  setvbuf(stdout, NULL, _IONBF, 0);

  int opt;
  while ((opt = getopt(argc, argv, "t:p:")) != -1) {
    switch (opt) {
      case 't':
        number_of_seconds_to_hammer = atoi(optarg);
        break;
      case 'p':
        fraction_of_physical_memory = atof(optarg);
        break;
      default:
        fprintf(stderr, "Usage: %s [-t nsecs] [-p percent]\n", 
            argv[0]);
        exit(EXIT_FAILURE);
    }
  }

  signal(SIGALRM, HammeredEnough);

  printf("[!] Starting the testing process...\n");
  alarm(number_of_seconds_to_hammer);
  HammerAllReachableRows(&HammerAddressesStandard, number_of_reads);
}

