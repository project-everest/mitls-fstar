module TLS13.Impl.Server.Schedule

#lang-pulse

open Pulse.Lib.Pervasives

module CS = TLS13.Spec.ConnectionState
module CR = TLS13.Impl.ConnectionState.Repr
module ST = TLS13.Impl.Server.Types

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

fn next_local_action
  (s:server)
  requires connection_exactly s 'st0 **
           pure (ST.server_state_correct 'st0)
  returns action:ST.next_local_action
  ensures connection_exactly s 'st0 **
          pure (ST.server_state_correct 'st0 /\
                ST.next_local_action_sound 'st0 action)
