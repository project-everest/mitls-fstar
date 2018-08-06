#pragma warning(disable:4057) // 'function': 'uint8_t *' differs in indirection to slightly different base types from 'char *'
#pragma warning(disable:4100) // 'cv': unreferenced formal parameter
#pragma warning(disable:4101) // 'p_': unreferenced local variable
#pragma warning(disable:4127) // warning C4127: conditional expression is constant
#pragma warning(disable:4146) // unary minus operator applied to unsigned type, result still unsigned
#pragma warning(disable:4189) // 'uu____187': local variable is initialized but not referenced
#pragma warning(disable:4201) // nonstandard extension used: nameless struct/union
#pragma warning(disable:4204) // nonstandard extension used: non-constant aggregate initializer
#pragma warning(disable:4211) // nonstandard extension used: redefined extern to static
#pragma warning(disable:4267) // 'initializing': conversion from 'size_t' to 'uint32_t', possible loss of data
#pragma warning(disable:4293) // '<<': shift count negative or too big, undefined behavior
#pragma warning(disable:4554) // '>>': check operator precedence for possible error; use parentheses to clarify precedence

#ifdef _KERNEL_MODE
#include <ntverp.h>
#include <ntosp.h>
#include <ntstrsafe.h>
#else
#include <windows.h>
#endif
__declspec(noreturn) extern void KremlExit(int n);

#define USE_HEAP_REGIONS 1
#include "RegionAllocator.h"

#define KRML_HOST_PRINTF DbgPrint
#define KRML_HOST_EPRINTF DbgPrint

