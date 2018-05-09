#include <memory.h>
#include <stdio.h>
#if __APPLE__
#include <sys/errno.h> // OS/X only provides include/sys/errno.h
#include <stdlib.h>
#else
#include <malloc.h>
#include <errno.h> // MinGW only provides include/errno.h
#endif
#if defined(_MSC_VER)
  #define IS_WINDOWS 1
  #ifdef _KERNEL_MODE
    #include <nt.h>
    #include <ntrtl.h>
  #else
    #include <windows.h>
  #endif
#elif defined(__MINGW32__)
  #define IS_WINDOWS 1
  #include <windows.h>
#else // Linux or gcc/cygwin
  #define IS_WINDOWS 0
  #include <pthread.h>
  #include <sys/queue.h>
#endif

#include "RegionAllocator.h"

#if REGION_STATISTICS

typedef struct _region_statistics {
    size_t current_bytes;   // bytes currently allocated
    size_t total_bytes;     // total of all allocations
    size_t peak_bytes;      // max value of current_bytes
    size_t allocation_count;// count of allocations made
    size_t free_count;      // count of frees made
    size_t allocation_failures; // count of allocation fails due to OOM
} region_statistics;

#ifndef KRML_HOST_PRINTF
#define KRML_HOST_PRINTF printf
#endif

void PrintRegionStatistics(HEAP_REGION rgn, region_statistics *stats)
{
    KRML_HOST_PRINTF("==== Statistics for Region %p ====\n", rgn);
    KRML_HOST_PRINTF("Current bytes:    %p\n", (void*)stats->current_bytes);
    KRML_HOST_PRINTF("Peak bytes:       %p\n", (void*)stats->peak_bytes);
    KRML_HOST_PRINTF("Total bytes:      %p\n", (void*)stats->total_bytes);
    KRML_HOST_PRINTF("Allocation count: %p\n", (void*)stats->allocation_count);
    KRML_HOST_PRINTF("Free count:       %p\n", (void*)stats->free_count);
    KRML_HOST_PRINTF("========\n");
}

void UpdateStatisticsAfterMalloc(region_statistics *stats, void *pv, size_t cb)
{
    stats->allocation_count++;
    if (pv) {
        stats->current_bytes += cb;
        stats->total_bytes += cb;
        if (stats->peak_bytes < stats->current_bytes) {
            stats->peak_bytes = stats->current_bytes;
        }
    } else {
        stats->allocation_failures++;
    }
}

void UpdateStatisticsAfterFree(region_statistics *stats, size_t cb)
{
    stats->current_bytes -= cb;
    stats->free_count++;
}
#else
#define UpdateStatisticsAfterMalloc(stats, pv, cb)
#define UpdateStatisticsAfterFree(stats, cb)
#define PrintRegionStatistics(rgn, stats)

#endif

#if USE_HEAP_REGIONS

#if IS_WINDOWS
typedef struct _region {
    HANDLE heap;
#if !defined(_MSC_VER)
    jmp_buf *penv;
#endif
#if REGION_STATISTICS
    region_statistics stats;
#endif
} region;

DWORD g_region_heap_slot;
region g_global_region;

// Global initialization
// returns 0 for error, nonzero for success
int HeapRegionInitialize()
{
    g_region_heap_slot = TlsAlloc();
    if (g_region_heap_slot == 0xffffffff) {
        return 0;
    }
    HANDLE h = HeapCreate(0, 0, 0);
    if (h == NULL) {
        TlsFree(g_region_heap_slot);
        return 0;
    }
    memset(&g_global_region, 0, sizeof(g_global_region));
    g_global_region.heap = h;
    return 1;
}
    
// Global termination.  Frees all memory in the global region.
void HeapRegionCleanup(void)
{
    PrintRegionStatistics(NULL, &g_global_region.stats);
    TlsFree(g_region_heap_slot);
    HeapDestroy(g_global_region.heap);
    g_region_heap_slot = 0;
}

// Create a new heap region
HEAP_REGION HeapRegionCreateAndRegister(HEAP_REGION *prgn
#if !defined(_MSC_VER)
  , jmp_buf *penv
#endif
)
{
    // Allocate a heap with:
    // - no internal locking
    // - a minimal initial commit (4kb)
    // - no maximum size - it can fill the entire address space if needed
    HANDLE h = HeapCreate(HEAP_NO_SERIALIZE, 0, 0);
    region *heap = HeapAlloc(h, 0, sizeof(region));
    memset(heap, 0, sizeof(*heap));
    heap->heap = h;
    // Make it the heap for this callgraph
    HEAP_REGION oldrgn = HeapRegionEnter(heap
#if !defined(_MSC_VER)
        ,penv
#endif
    );
    
    *prgn = heap;
    return oldrgn;
}

// Destroy a heap region, freeing all of its allocations
void HeapRegionDestroy(HEAP_REGION rgn)
{
    region *heap = (region*)rgn;
    HANDLE h = heap->heap;
    PrintRegionStatistics(heap, &heap->stats);
    HeapDestroy(h);
}

void PrintHeapRegionStatistics(HEAP_REGION rgn)
{
    region *heap = (region*)rgn;
    if (heap == NULL) {
        heap = &g_global_region;
    }
    PrintRegionStatistics(heap, &heap->stats);
}

HEAP_REGION HeapRegionEnter(HEAP_REGION rgn
#if !defined(_MSC_VER)
  , jmp_buf *penv
#endif
)
{
    HEAP_REGION oldrgn = TlsGetValue(g_region_heap_slot);
    TlsSetValue(g_region_heap_slot, rgn);
#if !defined(_MSC_VER)
    region *heap = (region*)rgn;
    if (heap == NULL) {
        g_global_region.penv = penv;
    } else {
        heap->penv = penv;
    }
#endif
    return oldrgn;
}

void HeapRegionLeave(HEAP_REGION oldrgn)
{
    TlsSetValue(g_region_heap_slot, oldrgn);
}

// KRML_HOST_MALLOC
void* HeapRegionMalloc(size_t cb)
{
    region *heap = (region*)TlsGetValue(g_region_heap_slot);
    if (heap == NULL) {
        heap = &g_global_region;
    }
    void *pv = HeapAlloc(heap->heap, 0, cb);
    UpdateStatisticsAfterMalloc(&heap->stats, pv, cb);
    if (pv == NULL) {
#if defined(_MSC_VER)
        RaiseException((DWORD)MITLS_OUT_OF_MEMORY_EXCEPTION, EXCEPTION_NONCONTINUABLE, 0, NULL);
#else
        longjmp(*heap->penv, 1);
#endif
    }
    
    return pv;
}

// KRML_HOST_CALLOC
void* HeapRegionCalloc(size_t num, size_t size)
{
    size_t cb = num*size;
    if (num != 0 && (cb/num) != size) {
        return NULL; // Integer overflow
    }
    void *pv = HeapRegionMalloc(cb);
    memset(pv, 0, cb);

    return pv;
}

// KRML_HOST_FREE
void HeapRegionFree(void* pv)
{
    if (pv == NULL) {
        return;
    }
    region *heap = (region*)TlsGetValue(g_region_heap_slot);
    if (heap == NULL) {
        heap = &g_global_region;
    }
#if REGION_STATISTICS
    size_t cb = HeapSize(heap->heap, 0, pv);
    UpdateStatisticsAfterFree(&heap->stats, cb);
#endif    
    if (!HeapFree(heap->heap, 0, pv)) {
        // This can happen if allocating from one region and freeing from another
        KRML_HOST_PRINTF("HeapRegionFree of %p from heap %p failed.\n", pv, heap);
    }
}

#else // !IS_WINDOWS
pthread_key_t g_region_heap_slot;
pthread_mutex_t g_global_region_lock; 

typedef struct region_allocation {
    LIST_ENTRY(region_allocation) entry;
#if REGION_STATISTICS
    size_t cb;
    size_t pad; // pad so this size is a multiple of 16 on 64-bit machines
#endif
} region_allocation;

typedef struct region {
    LIST_HEAD(region_allocation_list, region_allocation) entries;
    jmp_buf *penv;
#if REGION_STATISTICS
    region_statistics stats;
#endif    
} region;

region g_global_region; // All allocations made at global scope go here

// Global initialization  
// returns 0 for error, nonzero for success
int HeapRegionInitialize()
{
    if (pthread_mutex_init(&g_global_region_lock, NULL) != 0) {
        return 0;
    }
    if (pthread_key_create(&g_region_heap_slot, NULL) != 0) {
        pthread_mutex_destroy(&g_global_region_lock);
        return 0;
    }
    memset(&g_global_region, 0, sizeof(g_global_region));
    LIST_INIT(&g_global_region.entries);
    return 1;
}
    
// Global termination
void HeapRegionCleanup(void)
{
    HeapRegionDestroy((HEAP_REGION)&g_global_region);
    pthread_key_delete(g_region_heap_slot);
    pthread_mutex_destroy(&g_global_region_lock);
}

// Create a new region and make it this thread's default
HEAP_REGION HeapRegionCreateAndRegister(HEAP_REGION *prgn, jmp_buf *penv)
{
    HEAP_REGION oldrgn = (HEAP_REGION)pthread_getspecific(g_region_heap_slot);
    region *p = malloc(sizeof(region));
    if (p) {
        memset(p, 0, sizeof(region));
        LIST_INIT(&p->entries);
        p->penv = penv;
        pthread_setspecific(g_region_heap_slot, p);
    }
    *prgn = (HEAP_REGION)p;
    return oldrgn;
}

// Destroy a region and free all of its memory
void HeapRegionDestroy(HEAP_REGION rgn)
{
    pthread_setspecific(g_region_heap_slot, NULL);
    
    // Free all of the entries in the linked-list
    region *p = (region *)rgn;   
    PrintRegionStatistics(p, &p->stats);
    while (p->entries.lh_first) {
        struct region_allocation *a = p->entries.lh_first;
        LIST_REMOVE(a, entry);
        free(a);
    }
    if (p != &g_global_region) {
        // Then free the list head itself
        free(p);
    }
}

void PrintHeapRegionStatistics(HEAP_REGION rgn)
{
    region *heap = (region*)rgn;
    if (heap == NULL) {
        heap = &g_global_region;
    }
    PrintRegionStatistics(heap, &heap->stats);
}

HEAP_REGION HeapRegionEnter(HEAP_REGION rgn, jmp_buf *penv)
{
    HEAP_REGION oldrgn = (HEAP_REGION)pthread_getspecific(g_region_heap_slot);
    pthread_setspecific(g_region_heap_slot, rgn);
    region *heap = (region*)rgn;
    if (heap == NULL) {
        g_global_region.penv = penv;
    } else {
        heap->penv = penv;
    }
    return oldrgn;
}

void HeapRegionLeave(HEAP_REGION oldrgn)
{
    pthread_setspecific(g_region_heap_slot, oldrgn);
}

// KRML_HOST_MALLOC
void* HeapRegionMalloc(size_t cb)
{
    size_t actual_cb = cb + sizeof(struct region_allocation);
    if (actual_cb < cb) {
        return NULL; // Integer overflow
    }
    void *pv = malloc(actual_cb);
    region *heap = (region *)pthread_getspecific(g_region_heap_slot);
    if (pv) {
        struct region_allocation *e = (struct region_allocation*)pv;
#if REGION_STATISTICS
        e->cb = cb;
#endif
        if (heap == NULL) {
            pthread_mutex_lock(&g_global_region_lock);
            LIST_INSERT_HEAD(&g_global_region.entries, e, entry);
            UpdateStatisticsAfterMalloc(&g_global_region.stats, pv, cb);
            pthread_mutex_unlock(&g_global_region_lock);
        } else {
            UpdateStatisticsAfterMalloc(&heap->stats, pv, cb);
            LIST_INSERT_HEAD(&heap->entries, e, entry);
        }
        return (void*)(e + 1); // Return the address of the byte following the LIST_ENTRY
    }
    else {
        UpdateStatisticsAfterMalloc(&heap->stats, pv, cb);
        longjmp(*heap->penv, 1);
        return NULL;
    }
}

// KRML_HOST_CALLOC
void* HeapRegionCalloc(size_t num, size_t size)
{
    size_t cb = num*size;
    if (num != 0 && (cb/num) != size) {
        return NULL; // Integer overflow
    }
    void *pv = HeapRegionMalloc(cb);
    if (pv) {
        memset(pv, 0, cb);
    }
    return pv;
}

// KRML_HOST_FREE
void HeapRegionFree(void* pv)
{
    if (pv == NULL) {
        return;
    }
    region_allocation *e = ((region_allocation*)pv - 1);
    region *heap = (region*)pthread_getspecific(g_region_heap_slot);
    if (heap == NULL) {
        pthread_mutex_lock(&g_global_region_lock);
        LIST_REMOVE(e, entry);
        UpdateStatisticsAfterFree(&g_global_region.stats, e->cb);
        pthread_mutex_unlock(&g_global_region_lock);
    } else {
        LIST_REMOVE(e, entry);
        UpdateStatisticsAfterFree(&heap->stats, e->cb);
    }
    free(e);
}

#endif // !defined(_MSC_VER)
    

// End of USE_PROCESS_HEAP
#elif USE_KERNEL_REGIONS

#define MITLS_TAG 'LTmi'

LIST_ENTRY g_mapping_list; // list of region_entry
FAST_MUTEX g_mapping_lock;

typedef struct _region {
    LIST_ENTRY entries;
#if REGION_STATISTICS
    region_statistics stats;
#endif    
} region;

typedef struct _region_allocation {
    LIST_ENTRY entry;
#if REGION_STATISTICS
    size_t cb;
    size_t pad; // pad so this size is a multiple of 16 on 64-bit machines
#endif
} region_allocation;

EX_PUSH_LOCK global_region_lock;
region g_global_region; // All allocations made at global scope go here

// Global initialization
// returns 0 for error, nonzero for success
int HeapRegionInitialize()
{
    InitializeListHead(&g_mapping_list);
    ExInitializeFastMutex(&g_mapping_lock);
    ExInitializePushLock(&global_region_lock);
    RtlZeroMemory(&g_global_region, sizeof(g_global_region));
    InitializeListHead(&g_global_region.entries);
    return 1;
}
    
// Global termination
void HeapRegionCleanup(void)
{
    // The mapping list should be empty
    NT_ASSERT(IsListEmpty(&g_mapping_list));
    HeapRegionDestroy(&g_global_region);
}

// Destroy a region, freeing all of its memory
void HeapRegionDestroy(HEAP_REGION rgn)
{
    region *heap = (region*)rgn;
    PrintRegionStatistics(rgn, &g_global_region.stats);
    // Free all of the entries in the linked-list
    while (!IsListEmpty(&heap->entries)) {
        LIST_ENTRY *a = RemoveHeadList(&heap->entries);
        ExFreePoolWithTag(a, MITLS_TAG);
    }
    if (rgn != &g_global_region) {
        // Then free the list head itself
        ExFreePoolWithTag(heap, MITLS_TAG);
    }
}

// Create a new region-based heap and register it as the current region
void HeapRegionCreateAndRegister(region_entry* pe, HEAP_REGION *prgn)
{
    region *rgn = (region*)ExAllocatePoolWithTag(PagedPool, sizeof(region), MITLS_TAG);
    if (rgn) {
        InitializeListHead(&rgn->entries);
        HeapRegionRegister(pe, rgn);
    }
    *prgn = rgn;
}

// Associate the current thread ID with the region
void HeapRegionRegister(region_entry* pe, HEAP_REGION rgn)
{
    pe->id = PsGetCurrentThread();
    pe->region = rgn;
    ExAcquireFastMutex(&g_mapping_lock);
    InsertHeadList(&g_mapping_list, &pe->entry);
    ExReleaseFastMutex(&g_mapping_lock);
}

// Find the region for this thread ID, or return NULL for
// the global region.
LIST_ENTRY *HeapRegionFind(void)
{
    ExAcquireFastMutex(&g_mapping_lock);
    LIST_ENTRY *p = g_mapping_list.Flink;
    while (p != &g_mapping_list) {
        region_entry *r = CONTAINING_RECORD(p, region_entry, entry);
        if (r->id == PsGetCurrentThread()) {
            ExReleaseFastMutex(&g_mapping_lock);
            return r->region;
        }
        p = p->Flink;
    }
    ExReleaseFastMutex(&g_mapping_lock);    
    return NULL;
}

// Unregister this thread's active region
void HeapRegionUnregister(region_entry* pe)
{
    ExAcquireFastMutex(&g_mapping_lock);
    RemoveEntryList(&pe->entry);
    ExReleaseFastMutex(&g_mapping_lock);
}

void PrintHeapRegionStatistics(HEAP_REGION rgn)
{
    region *heap = (region*)rgn;
    if (heap == NULL) {
        heap = &g_global_region;
    }
    PrintRegionStatistics(heap, &heap->stats);
}

// KRML_HOST_MALLOC
void* HeapRegionMalloc(size_t cb)
{
    size_t actual_cb = cb + sizeof(region_allocation);
    if (actual_cb < cb) {
        return NULL; // Integer overflow
    }
    void *pv = ExAllocatePoolWithTag(PagedPool, actual_cb, MITLS_TAG);
    if (pv) {
        region_allocation *e = (region_allocation*)pv;
#if REGION_STATISTICS
        e->cb = cb;
#endif
        LIST_ENTRY *heap = HeapRegionFind();
        if (heap == NULL) {
            ExfAcquirePushLockExclusive(&global_region_lock);
            InsertHeadList(&g_global_region.entries, &e->entry);
            UpdateStatisticsAfterMalloc(&g_global_region.stats, pv, cb);
            ExfReleasePushLockExclusive(&global_region_lock);
        } else {
            InsertHeadList(heap, &e->entry);
            UpdateStatisticsAfterMalloc(&heap->stats, pv, cb);
        }
        return (void*)(e + 1); // Return the address of the byte following the LIST_ENTRY
    }
    else {
        RtlRaiseStatus(MITLS_OUT_OF_MEMORY_EXCEPTION);
        return NULL;
    }
}

// KRML_HOST_CALLOC
void* HeapRegionCalloc(size_t num, size_t size)
{
    size_t cb = num*size;
    if (num != 0 && (cb/num) != size) {
        return NULL; // Integer overflow
    }
    void *pv = HeapRegionMalloc(cb);
    if (pv) {
        RtlZeroMemory(pv, cb);
    }
    return pv;
}

// KRML_HOST_FREE
void HeapRegionFree(void* pv)
{
    if (pv == NULL) {
        return;
    }
    region_allocation *e = ((region_allocation*)pv - 1);
    LIST_ENTRY *heap = HeapRegionFind();

    if (heap == NULL) {
        ExfAcquirePushLockExclusive(&global_region_lock);
        RemoveEntryList(&e->entry);
        UpdateStatisticsAfterFree(&g_global_region.stats, e->cb);
        ExfReleasePushLockExclusive(&global_region_lock);
    } else {
        RemoveEntryList(&e->entry);
        UpdateStatisticsAfterFree(&heap->stats, e->cb);
    }
    ExFreePoolWithTag(e, MITLS_TAG);
}

// Non-region-based allocator, called by HACL*
void *KrmlAlloc(size_t cb)
{
    return ExAllocatePoolWithTag(PagedPool, cb, MITLS_TAG);
}

// Non-region-based allocator, called by HACL*
void* KrmlCAlloc(size_t num, size_t size)
{
    size_t cb = num*size;
    if (num != 0 && (cb/num) != size) {
        return NULL; // Integer overflow
    }
    void *pv = KrmlAlloc(cb);
    if (pv) {
        RtlZeroMemory(pv, cb);
    }
    return pv;
}

// Non-region-based allocator, called by HACL*
void KrmlFree(void* pv)
{
    ExFreePoolWithTag(pv, MITLS_TAG);
}

__declspec(noreturn) void KrmlExit(int n)
{
    EXCEPTION_RECORD e;

    e.ExceptionCode = STATUS_INTERNAL_ERROR;
    e.ExceptionFlags = EXCEPTION_NONCONTINUABLE;
    e.ExceptionAddress = (PVOID)KrmlExit;
    e.ExceptionRecord = NULL;
    e.NumberParameters = 1;
    e.ExceptionInformation[0] = (ULONG_PTR)n;
    RtlRaiseException(&e);
}

// return the time since Jan 1, 1970, in seconds.  Used by miTLS nonce code.
int KrmlTime(void)
{
    const __int64 EpochBias = 116444736000000000i64; // in milliseconds, from year 1600
    LARGE_INTEGER li;
    KeQuerySystemTime(&li);
    __int64 Milliseconds = li.QuadPart / 10000;
    return (int)((Milliseconds - EpochBias) / 1000i64);
}

// End of USE_KERNEL_REGIONS
#else //USE_PROCESS_HEAP

// Perform per-process initialization
// returns 0 for error, nonzero for success
int HeapRegionInitialize(void)
{
    return 1;
}

// Perform per-process termination
void HeapRegionCleanup(void)
{
}

// KRML_HOST_MALLOC/CALLOC/FREE plug-ins
void* HeapRegionMalloc(size_t cb)
{
    return malloc(cb);
}

void* HeapRegionCalloc(size_t num, size_t size)
{
    return calloc(num, size);
}

void HeapRegionFree(void* pv)
{
    free(pv);
}
#endif
