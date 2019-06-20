/* This allows running with a region allocator whose implementation is in
 * RegionAllocator.c... but we don't enable it in the default configuration. */

#include <stdlib.h>
#include <stdint.h>
#include "RegionAllocator.h"

#define KRML_HOST_MALLOC HeapRegionMalloc
#define KRML_HOST_CALLOC HeapRegionCalloc
#define KRML_HOST_FREE HeapRegionFree
