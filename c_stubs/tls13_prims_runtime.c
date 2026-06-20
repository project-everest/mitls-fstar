/* Hand-written definitions for the F* integer/uint8 runtime symbols that
   KaRaMeL leaves abstract in the extracted TLS bundles.

   The generated internal/FStar_PulseCore_Prims.h declares exactly these
   functions for current client/server driver bundles. */

#include "krmllib.h"

krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y)
{
  return x - y;
}

krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y)
{
  return x % y;
}

uint8_t FStar_UInt8_uint_to_t(krml_checked_int_t x)
{
  return (uint8_t)x;
}

krml_checked_int_t FStar_UInt8_v(uint8_t x)
{
  return (krml_checked_int_t)x;
}
