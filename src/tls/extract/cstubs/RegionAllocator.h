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

#if defined(_MSC_VER) || defined(__MINGW32__)
#define IS_WINDOWS 1
#else
#define IS_WINDOWS 0
#endif

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
#if IS_WINDOWS
  #define FACILITY_EVEREST 255
  #define CODE_OUT_OF_MEMORY 5
  #define MITLS_OUT_OF_MEMORY_EXCEPTION MAKE_HRESULT(1,FACILITY_EVEREST,CODE_OUT_OF_MEMORY)
  
  #define ENTER_GLOBAL_HEAP_REGION() ENTER_HEAP_REGION(NULL)

  #define LEAVE_GLOBAL_HEAP_REGION() \
    } __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
        HadHeapException = 1; \
    }

  #define ENTER_HEAP_REGION(rgn) \
    HeapRegionEnter(rgn); \
    char HadHeapException = 0; \
    __try {

  #define LEAVE_HEAP_REGION() \
    } __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
        HadHeapException = 1; \
    } \
    HeapRegionLeave();

  #define CREATE_HEAP_REGION(prgn) \
    HeapRegionCreateAndRegister(prgn); \
    char HadHeapException = 0; \
    __try {

  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)
  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)
  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)
  void HeapRegionEnter(HEAP_REGION rgn);
#else
  #include <setjmp.h>

  #define ENTER_GLOBAL_HEAP_REGION() ENTER_HEAP_REGION(NULL)
  #define LEAVE_GLOBAL_HEAP_REGION() }

  #define ENTER_HEAP_REGION(rgn) \
    jmp_buf jmp_buf_out_of_memory; \
    char HadHeapException = 0; \
    HeapRegionEnter(rgn, &jmp_buf_out_of_memory); \
    if (setjmp(jmp_buf_out_of_memory)) { \
      HadHeapException = 1; \
    } else {
  #define LEAVE_HEAP_REGION()    } HeapRegionLeave()
  #define CREATE_HEAP_REGION(prgn)   HeapRegionCreateAndRegister(prgn); {
  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)
  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)
  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)
  void HeapRegionEnter(HEAP_REGION rgn, jmp_buf* penv);
#endif
void HeapRegionLeave(void);
void HeapRegionCreateAndRegister(HEAP_REGION *prgn);
void HeapRegionDestroy(HEAP_REGION rgn);

#elif USE_KERNEL_REGIONS
// Use regions managed within the kernel pool.  All unfreed allocations within
// the region will be freed when the region is destroyed.  A default region
// holds allocations made outside of ENTER/LEAVE.  It will be freed when
// the region allocator is cleaned up.
#if IS_WINDOWS
  #define FACILITY_EVEREST 255
  #define CODE_OUT_OF_MEMORY 5
  #define MITLS_OUT_OF_MEMORY_EXCEPTION MAKE_HRESULT(1,FACILITY_EVEREST,CODE_OUT_OF_MEMORY)
  
  typedef struct {
    LIST_ENTRY entry; // dlist of region_entry
    PETHREAD id;
    void *region;     // ptr to dlist of actual pool allocations
  } region_entry;

  #define ENTER_GLOBAL_HEAP_REGION() \
    char HadHeapException = 0; \
    __try {

  #define LEAVE_GLOBAL_HEAP_REGION() \
    __except (GetExceptionCode() == MITLS_OUT_OF_MEMORY_EXCEPTION) { \
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
    HeapRegionCreateAndRegister(&e, (prgn));

  #define VALID_HEAP_REGION(rgn)    ((rgn) != NULL)

  #define DESTROY_HEAP_REGION(rgn) HeapRegionDestroy(rgn)

  #define HAD_OUT_OF_MEMORY         (HadHeapException != 0)

  void HeapRegionCreateAndRegister(region_entry* pe, HEAP_REGION *prgn);
  void HeapRegionRegister(region_entry* pe, HEAP_REGION rgn);
  void HeapRegionUnregister(region_entry* pe);
  void HeapRegionDestroy(HEAP_REGION rgn);
#else
  #error Non-Windows support is NYY
#endif

#else
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

#endif

#endif // HEADER_REGIONALLOCATOR_H
