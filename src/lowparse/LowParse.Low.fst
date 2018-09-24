module LowParse.Low
include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Low.Int
include LowParse.Low.List
include LowParse.Low.FLData
include LowParse.Low.Array
include LowParse.Low.Bytes
include LowParse.Low.VLData
include LowParse.Low.Enum
include LowParse.Low.Option

instance _ = {
  error_flbytes_not_enough_input = (-1l);
}

instance _ = {
  error_enum_unknown_key = (-2l);
}

instance _ = {
  error_vldata_not_enough_size_input = (-3l);
  error_vldata_size_out_of_bounds = (-4l);
  error_vldata_not_enough_payload_input = (-5l);
  error_vldata_not_enough_consumed_payload_input = (-6l);
}

instance _ = {
  error_fldata_not_enough_input = (-7l);
  error_fldata_not_enough_consumed_input = (-8l);
}

instance _ = {
  error_int_not_enough_input = (-9l);
}

instance _ = {
  error_total_constant_size_not_enough_input = (-10l);
}

module M = LowStar.Buffer
module G = FStar.Ghost

inline_for_extraction
let default_validator32_cls : validator32_cls = {
  validator32_error_gloc = G.hide M.loc_none;
  validator32_error_inv = (fun _ -> True);
  validator32_error_inv_loc_not_unused_in = (fun _ -> ());
  validator32_error_inv_frame = (fun _ _ _ -> ());
}

inline_for_extraction
let buffer_validator32_cls (#t: Type) (b: M.buffer t) : Tot validator32_cls = {
  validator32_error_gloc = G.hide (M.loc_buffer b);
  validator32_error_inv = (fun h -> M.live h b);
  validator32_error_inv_loc_not_unused_in = (fun _ -> ());
  validator32_error_inv_frame = (fun _ _ _ -> ());
}

module B = LowStar.Buffer
module I32 = FStar.Int32

inline_for_extraction
let report_validation_error_gen
  (#error_log_t: Type)
  (transform_error: (error_log_t -> Tot error_log_t))
  (b: M.pointer error_log_t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator32 #(buffer_validator32_cls b) p)
: Tot (validator32 #(buffer_validator32_cls b) p)
= fun input len ->
  let res = v input len in
  begin if res `I32.lt` 0l
  then
    let r = B.index b 0ul in
    B.upd b 0ul (transform_error r)
  end;
  res

inline_for_extraction
let append_validation_error
  (#error_log_t: Type)
  (append: (error_log_t -> error_log_t -> Tot error_log_t))
  (x: error_log_t)
= report_validation_error_gen (fun x0 -> append x0 x)

inline_for_extraction
let report_first_validation_error
  (#error_log_t: Type)
  (x: error_log_t)
= report_validation_error_gen (fun x0 -> match x0 with None -> Some x | _ -> x0)
