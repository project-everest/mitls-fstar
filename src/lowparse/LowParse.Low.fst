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
