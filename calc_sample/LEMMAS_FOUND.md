# Key F* Library Lemmas for Eliminating Admits

## From Repository Search

### 1. Big-Endian Encoding (FStar.UInt, FStar.Int.Cast)

#### Cast Module Postconditions
```fstar
// From FStar.Int.Cast.fst
val uint8_to_uint32: a:U8.t -> Tot (b:U32.t{U32.v b = U8.v a})
val uint32_to_uint8: a:U32.t -> Tot (b:U8.t{U8.v b = U32.v a % pow2 8})
```

**Key insight**: Cast functions already have precise postconditions!
- `uint8_to_uint32`: Preserves value exactly
- `uint32_to_uint8`: Takes modulo 256

#### Shift-Right Lemmas  
```fstar
// From FStar.UInt.fsti
val shift_right_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (ensures shift_right #n a s = a / pow2 s)

val shift_right_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (ensures shift_right #n a 0 = a / pow2 0)

val shift_right_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (ensures shift_right #n a s = a / pow2 s)
```

**Key insight**: `shift_right a s = a / pow2 s` for all valid `s`!

#### Application to our admits:

For **write_result_response** (Admit #3):
1. Use `shift_right_value_aux_*` to show: `U32.v (shift_right value 24) = U32.v value / pow2 24`
2. Since `pow2 24 = 16777216`, we get: `U32.v (shift_right value 24) = U32.v value / 16777216`
3. Use `uint32_to_uint8` postcondition: `U8.v (uint32_to_uint8 x) = U32.v x % 256`
4. Combine: `U8.v b1 = (U32.v value / 16777216) % 256`
5. Repeat for shifts 16, 8, 0
6. Then prove big-endian decomposition equals original value

For **parse_push_value** (Admit #4):
1. Use `uint8_to_uint32` postcondition: `U32.v (uint8_to_uint32 b) = U8.v b`
2. U32 arithmetic: `v0*16777216 + v1*65536 + v2*256 + v3`
3. Prove sum < 2^32 (each component bounded)
4. Therefore modular arithmetic is identity
5. Equals `be_to_n` definition

---

### 2. Sequence Append/Slice (FStar.Seq.Properties)

#### Key Lemmas
```fstar
// From FStar.Seq.Properties.fsti
val lemma_slice_append: #a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> 
  Lemma (ensures (equal (append s1 s2) 
                        (append (slice s1 0 1) 
                                (append (slice s1 1 (length s1)) s2))))

val lemma_slice_first_in_append: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i <= length s1} -> 
  Lemma (ensures (equal (slice (append s1 s2) i (length (append s1 s2))) 
                        (append (slice s1 i (length s1)) s2)))
```

**Key insight**: `lemma_slice_first_in_append` directly proves what we need!

For **lemma_parse_requests_append_one** (Admit #2):
```fstar
// We need: slice (append bytes1 msg_bytes) 5 len == append (slice bytes1 5 len1) msg_bytes
// This is EXACTLY lemma_slice_first_in_append with i=5!

let rec lemma_parse_requests_append_one bytes1 msg_bytes req =
  if Seq.length bytes1 < 5 then ()
  else begin
    let rest1 = Seq.slice bytes1 5 (Seq.length bytes1) in
    lemma_parse_requests_append_one rest1 msg_bytes req;
    
    // Key step: use library lemma
    Seq.Properties.lemma_slice_first_in_append bytes1 msg_bytes 5;
    // Now we know: slice (append bytes1 msg_bytes) 5 len == append rest1 msg_bytes
    
    // Rest follows by induction
  end
```

---

### 3. Additional Useful Lemmas

#### FStar.Math.Lemmas (for arithmetic)
```fstar
// Useful for proving big-endian decomposition
val modulo_lemma: a:int -> b:pos -> Lemma (a % b >= 0 /\ a % b < b)
val division_multiplication_lemma: a:nat -> b:pos -> q:nat -> r:nat ->
  Lemma (requires a = q * b + r /\ r < b)
        (ensures a / b = q /\ a % b = r)
val pow2_plus: n:nat -> m:nat -> Lemma (pow2 (n + m) == pow2 n * pow2 m)
```

#### Calc Proofs (for multi-step reasoning)
```fstar
calc (==) {
  (U32.v value / 16777216) % 256 * 16777216 +
  (U32.v value / 65536) % 256 * 65536 +
  (U32.v value / 256) % 256 * 256 +
  U32.v value % 256;
  == { lemma_big_endian_decomposition (U32.v value) }
  U32.v value;
}
```

---

## Implementation Strategy

### Priority 1: Big-Endian Encoding Admits (Easiest)

Create `calc_sample/spec/Calc.Wire.Lemmas.fst`:
```fstar
module Calc.Wire.Lemmas

open FStar.UInt
open FStar.UInt32
open FStar.UInt8
open FStar.Int.Cast
open FStar.Math.Lemmas

// Prove shift_right corresponds to division
let lemma_shift_right_24 (x: U32.t) 
  : Lemma (U32.v (U32.shift_right x 24ul) = U32.v x / 16777216)
  = FStar.UInt.shift_right_value_aux_3 #32 (U32.v x) 24

// Similarly for 16, 8

// Prove big-endian decomposition
let lemma_be_decomposition (x: nat{x < 4294967296})
  : Lemma ((x / 16777216) % 256 * 16777216 + ... == x)
  = // Use division_multiplication_lemma and arithmetic

// Combine into final lemma
let lemma_u32_to_be_bytes (value: U32.t) (bytes: bytes{...})
  : Lemma (be_to_n bytes == U32.v value)
  = lemma_shift_right_24 value;
    lemma_shift_right_16 value;
    // ...
    lemma_be_decomposition (U32.v value)
```

Then in Pulse code:
```pulse
fn write_result_response ...
{
  // ... write bytes ...
  Calc.Wire.Lemmas.lemma_u32_to_be_bytes value resp_bytes1
}
```

### Priority 2: Sequence Append (Medium)

In `Calc.Log.fst`:
```fstar
#push-options "--fuel 2 --ifuel 1"
let rec lemma_parse_requests_append_one bytes1 msg_bytes req =
  if Seq.length bytes1 < 5 then ()
  else begin
    let rest1 = Seq.slice bytes1 5 (Seq.length bytes1) in
    lemma_parse_requests_append_one rest1 msg_bytes req;
    
    // Use FStar.Seq.Properties.lemma_slice_first_in_append
    Seq.Properties.lemma_slice_first_in_append bytes1 msg_bytes 5;
    
    // The lemma tells us: slice (append bytes1 msg_bytes) 5 len == append rest1 msg_bytes
    // Therefore: parse_requests (slice (append bytes1 msg_bytes) 5 len)
    //          == parse_requests (append rest1 msg_bytes)  [by IH]
    //          == parse_requests rest1 @ [req]
  end
#pop-options
```

### Priority 3: Length Lemma (Harder - requires manual induction)

This one needs more careful induction hypothesis strengthening.

---

## Estimated Time with These Lemmas

- **Big-endian admits**: 2-3 hours → **30 minutes** (library lemmas do most work)
- **Sequence append**: 3-4 hours → **1 hour** (lemma_slice_first_in_append is key)
- **Length lemma**: 2-3 hours → **1.5 hours** (still needs manual work)

**Total**: ~3 hours instead of 10-13 hours!

---

## Key Takeaway

**The F* standard library already has most of what we need!**
- Cast functions have precise postconditions
- shift_right equals division by power of 2
- Sequence append/slice lemmas exist

The admits can be eliminated primarily by **using existing library lemmas**, not by proving everything from scratch.
