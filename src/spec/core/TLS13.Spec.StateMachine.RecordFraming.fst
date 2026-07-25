module TLS13.Spec.StateMachine.RecordFraming

(**
  TLS record-fragment counting shared by the audit-facing connection state
  machine and the legacy client trace projection. This leaf module has no
  dependency on either state-machine representation.
**)

module B = TLS13.Bytes

let max_application_data_fragment_len : nat = 16384

let rec application_data_record_count_len (len:nat) : Tot nat (decreases len) =
  if len <= max_application_data_fragment_len then 1
  else 1 + application_data_record_count_len (len - max_application_data_fragment_len)

let application_data_record_count (bytes:B.bytes) : nat =
  application_data_record_count_len (B.length bytes)

let lemma_application_data_record_count_len_small (len:nat)
  : Lemma
      (requires len <= max_application_data_fragment_len)
      (ensures application_data_record_count_len len == 1)
  =
  ()

let rec lemma_application_data_record_count_len_positive (len:nat)
  : Lemma
      (ensures 1 <= application_data_record_count_len len)
      (decreases len)
  =
  if len <= max_application_data_fragment_len then ()
  else lemma_application_data_record_count_len_positive (len - max_application_data_fragment_len)

let lemma_application_data_record_count_len_step (len:nat)
  : Lemma
      (requires max_application_data_fragment_len < len)
      (ensures application_data_record_count_len len ==
               1 + application_data_record_count_len (len - max_application_data_fragment_len))
  =
  ()
