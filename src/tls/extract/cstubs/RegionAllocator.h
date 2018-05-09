#ifndef HEADER_REGIONALLOCATOR_H
#define HEADER_REGIONALLOCATOR_H

/******
This file has multiple compilation options:
1.  Choice of region-based heap:
    - USE_HEAP_REGIONS - use region-based heaps in usermode.  On Windows, this
      leverages a separate heap instance per region, via CreateHeap().  On Linux,
      this manages a per-region linked-list of allocations made via malloc().
    - USE_KERNEL_REGIONS - Windows only.  Manage a per-region linked list of
      allocations made via ExAllocatePoolWithTag().
    - default... no-op.  All allocations are made without region tracking.
    
2.  REGION_STATISTICS.  If set, for both USE_HEAP_REGIONS and USE_KERNEL_REGIONS,
    then the allocator maintains per-region statistics, for total bytes
    allocated, peak bytes, count of allocations, etc.

******/

#include <stdlib.h> // for size_t

typedef void *HEAP_REGION;

// Perform per-process initialization
// returns 0 for error, nonzero for success
int HeapRegionInitialize(void);

// Perform per-process termination
void HeapRegionCleanup(void);

void PrintHeapRegionStatistics(HEAP_REGION rgn);

// KRML_HOST_MALLOC/CALLOC/FREE plug-ins
void* HeapRegionMalloc(size_t cb);
void* HeapRegionCalloc(size_t num, size_t size);
void HeapRegionFree(void* pv);

#if USE_HEAP_REGIONS

// Use a per-region heap.  All unfreed allocations within the region will
// be freed when the region is destroyed.  A default region holds allocations
// made outside of ENTER/LEAVE.  It will be freed when the region allocator
// is cleaned up.
#if defined(_MSC_VER)
  #define FACILITY_EVEREST 255
  #define CODE_OUT_OF_MEMORY 5
  #define MITLS_OUT_OF_MEMORY_EXCEPTION MAKE_HRESULT(1,FACILITY_EVEREST,CODE_OUT_OF_MEMORY)
  
  #define ENTER_GLOBAL_HEAP_REGION() ENTER_HEAP_REGION(NULL)

  #define LEAVE_GLOBAL_HEAP_REGION() LEAVE_HEAP_REGION()

  #define ENTER_HEAP_REGION(rgn) \
    HEAP_REGION OldRegion = HeapRegionEnter(rgn); \
    char HadHeapException = 0; \
    __try {

  #define LEAVE_HEAP_REGION() \
    } __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
        HadHeapException = 1; \
    } \
    HeapRegionLeave(OldRegion);

  #define CREATE_HEAP_REGION(prgn) \
    HEAP_REGION OldRegion = HeapRegionCreateAndRegister(prgn); \
    char HadHeapException = 0; \
    __try {

  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)
  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)
  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)
  HEAP_REGION HeapRegionEnter(HEAP_REGION rgn);
  HEAP_REGION HeapRegionCreateAndRegister(HEAP_REGION *prgn);
#else // !defined(_MSC_VER), so mingw, gcc, etc.
  #include <setjmp.h>

  #define ENTER_GLOBAL_HEAP_REGION() ENTER_HEAP_REGION(NULL)
  #define LEAVE_GLOBAL_HEAP_REGION() LEAVE_HEAP_REGION()

  #define ENTER_HEAP_REGION(rgn) \
    jmp_buf jmp_buf_out_of_memory; \
    char HadHeapException = 0; \
    HEAP_REGION OldRegion = HeapRegionEnter(rgn, &jmp_buf_out_of_memory); \
    if (setjmp(jmp_buf_out_of_memory)) { \
      HadHeapException = 1; \
    } else {

  #define LEAVE_HEAP_REGION() \
    } \
    HeapRegionLeave(OldRegion)

  #define CREATE_HEAP_REGION(prgn) \
    jmp_buf jmp_buf_out_of_memory; \
    char HadHeapException = 0; \
    HEAP_REGION OldRegion = HeapRegionCreateAndRegister(prgn, &jmp_buf_out_of_memory); \
    if (setjmp(jmp_buf_out_of_memory)) { \
      HadHeapException = 1; \
    } else {

  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)
  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)
  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)
  HEAP_REGION HeapRegionEnter(HEAP_REGION rgn, jmp_buf* penv);
  HEAP_REGION HeapRegionCreateAndRegister(HEAP_REGION *prgn, jmp_buf* penv);
#endif // !defined(_MSC_VER), so mingw, gcc, etc.

void HeapRegionLeave(HEAP_REGION oldrgn);
void HeapRegionDestroy(HEAP_REGION rgn);

#elif USE_KERNEL_REGIONS
// Use regions managed within the kernel pool.  All unfreed allocations within
// the region will be freed when the region is destroyed.  A default region
// holds allocations made outside of ENTER/LEAVE.  It will be freed when
// the region allocator is cleaned up.
#if defined(_MSC_VER)
  #define MITLS_OUT_OF_MEMORY_EXCEPTION 0x80ff0005
  
  typedef struct {
    LIST_ENTRY entry; // dlist of region_entry
    PETHREAD id;
    void *region;     // ptr to dlist of actual pool allocations
  } region_entry;

  #define ENTER_GLOBAL_HEAP_REGION() \
    char HadHeapException = 0; \
    __try {

  #define LEAVE_GLOBAL_HEAP_REGION() \
    } __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
        HadHeapException = 1; \
    }

  #define ENTER_HEAP_REGION(rgn) \
    region_entry e; \
    HeapRegionRegister(&e, (rgn)); \
    char HadHeapException = 0; \
    __try {

  #define LEAVE_HEAP_REGION() \
    } __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
        HadHeapException = 1; \
    } \
    HeapRegionUnregister(&e);

  #define CREATE_HEAP_REGION(prgn) \
    region_entry e; \
    HeapRegionCreateAndRegister(&e, (prgn)); \
    char HadHeapException = 0; \
    __try {

  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)

  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)

  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)

  void HeapRegionCreateAndRegister(region_entry* pe, HEAP_REGION *prgn);
  void HeapRegionRegister(region_entry* pe, HEAP_REGION rgn);
  void HeapRegionUnregister(region_entry* pe);
  void HeapRegionDestroy(HEAP_REGION rgn);
#else // !defined(_MSC_VER)
  #error Non-Windows support is NYI
#endif //!defined(_MSC_VER)

#define KRML_HOST_MALLOC HeapRegionMalloc
#define KRML_HOST_CALLOC HeapRegionCalloc
#define KRML_HOST_FREE   HeapRegionFree

#else // !USE_HEAP_REGIONS && !USE_KERNEL_REGIONS
// Use the single process-wide heap.  All unfreed allocations will be leaked.

#ifndef TRUE
#include <stdbool.h>
#define TRUE true
#endif

#define ENTER_GLOBAL_HEAP_REGION()
#define LEAVE_GLOBAL_HEAP_REGION()
#define ENTER_HEAP_REGION(rgn)
#define LEAVE_HEAP_REGION()
#define CREATE_HEAP_REGION(prgn) *(prgn)=NULL
#define VALID_HEAP_REGION(rgn) TRUE
#define DESTROY_HEAP_REGION(rgn)
#define HAD_OUT_OF_MEMORY 0

#endif // !USE_HEAP_REGIONS && !USE_KERNEL_REGIONS

#endif // HEADER_REGIONALLOCATOR_H
