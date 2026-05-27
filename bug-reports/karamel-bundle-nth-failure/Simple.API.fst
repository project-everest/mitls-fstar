module Simple.API

open FStar.UInt32
module SI = Simple.Internal
module SS = Simple.State

// Top-level API module that uses Simple.Internal (similar to TLS13.Connection using TLS13.Handshake)

type connection = {
  state: SS.state;
  last_result: SI.result;
}

let create (init_val: t) : connection =
  { state = { value = init_val };
    last_result = SI.Success }

let process (c: connection) (msg: SI.message_type) : connection =
  let result = SI.process_message msg c.state.value in
  { c with last_result = result }

let get_threshold (msg: SI.message_type) : t =
  SI.get_threshold msg
