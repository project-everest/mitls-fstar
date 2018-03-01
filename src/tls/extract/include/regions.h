#include <stdlib.h>
#include <stdint.h>
#include "RegionAllocator.h"

#define KRML_HOST_MALLOC HeapRegionMalloc
#define KRML_HOST_CALLOC HeapRegionCalloc
#define KRML_HOST_FREE HeapRegionFree
