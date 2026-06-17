/* Hand-written C definitions for the [krml_checked_int_t] (F* mathematical
   integer / [nat]) runtime primitives that KaRaMeL leaves abstract.

   The verified TLS client still has some [nat]/[list] arithmetic in its
   hand-written spec/impl layer (e.g. Seq/list lengths), which KaRaMeL lowers to
   [krml_checked_int_t] and the [Prims.op_*] / [FStar.UInt8.v] primitives.  These
   are declared [extern] in the generated internal headers
   (e.g. internal/FStar_Pulse_PulseCore_Prims.h) and must be provided by the
   linker.

   Historically these definitions were injected (by the bundle post-processing
   step) into the KaRaMeL-generated FStar_Pulse_PulseCore_Prims.c.  That file is
   only emitted when something in the FStar.Pulse.PulseCore.Prims bundle is
   reachable; once the FStar.SizeT stub was removed (the client calls no
   FStar.SizeT function, so stock FStar.SizeT — with [v]/[uint_to_t] noextract —
   is used), that file is no longer generated.  Hosting the helpers here keeps
   them present regardless of KaRaMeL's reachability decisions. */

#include "krmllib.h"

krml_checked_int_t Prims_op_Division(krml_checked_int_t x, krml_checked_int_t y)
{
  return x / y;
}

krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y)
{
  return x - y;
}

krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y)
{
  return x + y;
}

krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y)
{
  return x % y;
}

bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y)
{
  return x <= y;
}

bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y)
{
  return x > y;
}

bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y)
{
  return x < y;
}

uint8_t FStar_UInt8_uint_to_t(krml_checked_int_t x)
{
  return (uint8_t)x;
}

krml_checked_int_t FStar_UInt8_v(uint8_t x)
{
  return (krml_checked_int_t)x;
}
