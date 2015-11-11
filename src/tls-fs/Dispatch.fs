(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Dispatch

open Bytes
open TLSConstants
open Tcp
open Error
open TLSError
open Handshake
open Alert
open TLSInfo
open Range
open TLSFragment

type predispatchState =
  | Init
  | FirstHandshake of TLSConstants.ProtocolVersion
  | Finishing
  | Finished (* Only for Writing side, useful if we were to allow TLS False Start *)
  | Open
  | Closing of ProtocolVersion * string
  | Closed

type dispatchState = predispatchState

type dState = {
    disp: dispatchState;
    conn: Record.ConnectionState;
    }
     
type preGlobalState = {
  (* abstract protocol states for HS/CCS, AL, and AD *)
  handshake: Handshake.hs_state;
  alert    : Alert.state;
  appdata  : AppData.app_state;

  (* connection state for reading and writing *)
  read  : dState;
  write : dState;

  (* The actual socket *)
  ns: NetworkStream;
  }

type globalState = preGlobalState

type preConnection = 
  | Conn of ConnectionInfo * globalState
type Connection = preConnection
let networkStream (Conn(id,g)) = g.ns

type nextCn = Connection
type nullCn = Connection
type query = Cert.chain
// FIXME: Put the following definitions close to range and delta, and use them
type msg_i = (range * DataStream.delta)
type msg_o = (range * DataStream.delta)

// Outcomes for internal, one-message-at-a-time functions
type writeOutcome =
    | WError of string (* internal *)
    | WriteAgain (* Possibly more data to send *)
    | WriteAgainFinishing (* Possibly more data to send, and the outgoing epoch changed *)
    | WriteAgainClosing (* An alert must be sent before the connection is torn down *)
    | WDone (* No more data to send in the current state *)
    | WAppDataDone (* App data have been sent, no more data to send *)
    | WriteFinished (* The finished message has been sent, but the handshake is not over *)
    | WHSDone (* The handshake is complete *)
    | SentFatal of alertDescription * string (* The alert we sent *)
    | SentClose

type readOutcome =
    | WriteOutcome of writeOutcome 
    | RError of string (* internal *)
    | RAgain
    | RAgainFinishing
    | RAppDataDone of msg_i
    | RQuery of query * bool
    | RFinished
    | RHSDone
    | RClose
    | RFatal of alertDescription (* The alert we received *)
    | RWarning of alertDescription (* The alert we received *)


let init ns role poptions =
    let hsInitRes = Handshake.init role poptions in
    let (ci,hs) = hsInitRes in
    let id_in = ci.id_in in
    let id_out = ci.id_out in
    let recv = Record.nullConnState id_in Reader in
    let send = Record.nullConnState id_out Writer in
    let read_state = {disp = Init; conn = recv} in
    let write_state = {disp = Init; conn = send} in
    let al = Alert.init ci in
    let app = AppData.init ci in
    let state = { handshake = hs;
                  alert = al;
                  appdata = app;
                  read = read_state;
                  write = write_state;
                  ns=ns;} in
    Conn ( ci, state)

let resume ns sid ops =
    (* Only client side, can never be server side *)
    let (ci,hs) = Handshake.resume sid ops in
    let send = Record.nullConnState ci.id_out Writer in
    let write_state = {disp = Init; conn = send} in
    let recv = Record.nullConnState ci.id_in  Reader in
    let read_state = {disp = Init; conn = recv} in
    let al = Alert.init ci in
    let app = AppData.init ci in
    let res = Conn ( ci,
                     { handshake = hs;
                       alert = al;
                       appdata = app;
                       read = read_state;
                       write = write_state;
                       ns = ns;}) in
    res

let rehandshake (Conn(id,conn)) ops =
    let (accepted,new_hs) = Handshake.rehandshake id conn.handshake ops in // Equivalently, id.id_in.sinfo
    let conn = {conn with handshake = new_hs} in
    (accepted,Conn(id,conn))

let rekey (Conn(id,conn)) ops =
    let (accepted,new_hs) = Handshake.rekey id conn.handshake ops in // Equivalently, id.id_in.sinfo
    let conn = {conn with handshake = new_hs} in
    (accepted,Conn(id,conn))

let request (Conn(id,conn)) ops =
    let (accepted,new_hs) = Handshake.request id conn.handshake ops in // Equivalently, id.id_in.sinfo
    (accepted,Conn(id,{conn with handshake = new_hs}))

let moveToOpenState (Conn(id,c)) =
    let read = c.read in
    match read.disp with
    | Finishing | Finished ->
        (let new_read = {read with disp = Open} in
        let c_write = c.write in
        match c_write.disp with
        | Finishing | Finished ->
            let new_write = {c_write with disp = Open} in
            let c = {c with read = new_read; write = new_write} in
            correct c
        | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ ""))
    | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "")

(* Dispatch dealing with network sockets *)
let pickSendPV (Conn(id,c)) =
    let c_write = c.write in
    match c_write.disp with
    | Init -> getMinVersion id c.handshake
    | FirstHandshake(pv) | Closing(pv,_) -> pv
    | Finishing | Finished | Open -> 
        let id_out = id.id_out in 
        let si = epochSI(id_out) in 
        si.protocol_version
    | Closed -> unexpected "[pickSendPV] invoked on a Closed connection"

let closeConnection (Conn(id,c)) =
    let new_read = {c.read with disp = Closed} in
    let new_write = {c.write with disp = Closed} in
    let new_hs = Handshake.invalidateSession id c.handshake in
    let c = {c with read = new_read;
                    write = new_write;
                    handshake = new_hs} in
    Conn(id,c)

let abortWithAlert (Conn(id,c)) ad reason =
    let closingPV = pickSendPV (Conn(id,c)) in
    let new_read = {c.read with disp = Closed} in
    let new_write = {c.write with disp = Closing(closingPV,reason)} in
    let new_hs = Handshake.invalidateSession id c.handshake in
    let new_alert = Alert.send_alert id c.alert ad in
    let c = {c with read = new_read;
                    write = new_write;
                    handshake = new_hs;
                    alert = new_alert} in
    (Conn(id,c))

let getReason dstate =
    match dstate with
    | Closing(_,reason) -> reason
    | _ -> ""

let send ns e write pv rg ct frag =
    let w_conn = write.conn in
    let res = Record.recordPacketOut e w_conn pv rg ct frag in
    let (conn,data) = res in
    let dState = {write with conn = conn} in
    match Tcp.write ns data with
    | Error(x) -> Error(AD_internal_error,x)
    | Correct(_) -> correct(dState)

(* which fragment should we send next? *)
(* we must send this fragment before restoring the connection invariant *)
let writeOne (Conn(id,c)) (ghost: option<(range * DataStream.delta * AppFragment.plain * DataStream.stream)>): writeOutcome * Connection =
  let c_write = c.write in
  match c_write.disp with
  | Closed -> let reason = perror __SOURCE_FILE__ __LINE__ "Trying to write on a closed connection" in (WError(reason), Conn(id,c))
  | _ ->
      let state = c.alert in
      match Alert.next_fragment id state with
      | (Alert.EmptyALFrag,_) -> 
          (let hs_state = c.handshake in
          let hs_next_res = Handshake.next_fragment id hs_state in
          match hs_next_res with 
          | Handshake.OutIdle(_) ->
                // only poll AppData if we're in Open state
                (match c_write.disp with
                | Open ->
                    let app_state = c.appdata in
                    (match (AppData.next_fragment id app_state, ghost) with
                    | None, None -> (WDone,Conn(id,c))
                    | Some (next), Some(_) ->
                        (let (tlen,f,new_app_state) = next in
                        (* we send some data fragment *)
                        let id_out = id.id_out in
                        let c_write_conn = c_write.conn in
                        let history = Record.history id_out Writer c_write_conn in
                        let frag = TLSFragment.appPlainToRecordPlain id_out history tlen f in
                        let pv = pickSendPV (Conn(id,c)) in
                        let resSend = send c.ns id_out c_write pv tlen Application_data frag in
                        match resSend with
                        | Correct(new_write) ->
                            let c = { c with appdata = new_app_state;
                                                write = new_write } in
                            (* Fairly, tell we're done, and we won't write more data *)
                            (WAppDataDone, Conn(id,c))

                        | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed) (* Unrecoverable error *))
                    | _,_ -> unexpected "[writeOne] invoked with inconsisten arguments")
                | _ ->
                    // We are finishing a handshake. Tell we're done, so that next read will complete the handshake.
                    (WDone,Conn(id,c)))

          //#begin-alertAttackSend
          | Handshake.OutCCS(rg,ccs,nextID,nextWrite,new_hs_state) ->
                    (let nextWCS = Record.initConnState nextID.id_out Writer nextWrite in
                    (* we send a (complete) CCS fragment *)
                    match c_write.disp with
                    | FirstHandshake(_) | Open ->
                        (let history = Record.history id.id_out Writer c_write.conn in
                        let ki = TLSInfo.mk_id id.id_out in
                        let es = HSFragment.init ki in
                        let hs = TLSFragment.ccsHistory id.id_out history in
                        let ccs = HSFragment.reStream ki es rg ccs hs in 
                        let frag = TLSFragment.ccsPlainToRecordPlain id.id_out history rg ccs in
                        let pv = pickSendPV (Conn(id,c)) in
                        let resSend = send c.ns id.id_out c.write pv rg Change_cipher_spec frag in
                        match resSend with
                        | Correct _ -> (* We don't care about next write state, because we're going to reset everything after CCS *)
                            (* Now:
                                - update the index and the state of other protocols
                                - move the outgoing state to Finishing, to signal we must not send appData now. *)
                            let new_write = {c.write with disp = Finishing; conn = nextWCS} in 
                            let new_ad = AppData.reset_outgoing id c.appdata nextID in
                            let new_al = Alert.reset_outgoing id c.alert nextID in
                            let c = { c with write = new_write;
                                             handshake = new_hs_state;
                                             alert = new_al;
                                             appdata = new_ad} in 
                            (WriteAgainFinishing, Conn(nextID,c))
                        | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
                    | _ -> (* Internal error: send a fatal alert to the other side *)
                        let reason = perror __SOURCE_FILE__ __LINE__ "Sending CCS in wrong state" in
                        let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in (WriteAgainClosing, closing))
          //#end-alertAttackSend
          | (Handshake.OutSome(rg,f,new_hs_state)) ->     
                      (* we send some handshake fragment *)
                      (match c_write.disp with
                      | Init | FirstHandshake(_) | Finishing | Open ->
                          (let history = Record.history id.id_out Writer c_write.conn in
                          let ki = TLSInfo.mk_id id.id_out in
                          let es = HSFragment.init ki in
                          let hs = TLSFragment.handshakeHistory id.id_out history in
                          let f = HSFragment.reStream ki es rg f hs in
                          let frag = TLSFragment.hsPlainToRecordPlain id.id_out history rg f in
                          let pv = pickSendPV (Conn(id,c)) in
                          let resSend = send c.ns id.id_out c.write pv rg Handshake frag in
                          match resSend with 
                          | Correct(new_write) ->
                            let c = { c with handshake = new_hs_state;
                                             write  = new_write } in
                            (WriteAgain, Conn(id,c))
                          | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
                      | _ -> (* Internal error: send a fatal alert to the other side *)
                        let reason = perror __SOURCE_FILE__ __LINE__ "Sending handshake messages in wrong state" in
                        let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in (WriteAgainClosing, closing))
          | (Handshake.OutFinished(rg,lastFrag,new_hs_state)) ->
                (* check we are in finishing state *)
                (match c_write.disp with
                | Finishing ->
                    (* Send the last fragment *)
                    (let history = Record.history id.id_out Writer c_write.conn in
                    let ki = TLSInfo.mk_id id.id_out in
                    let es = HSFragment.init ki in
                    let hs = TLSFragment.handshakeHistory id.id_out history in
                    let lastFrag = HSFragment.reStream ki es rg lastFrag hs in
                    let frag = TLSFragment.hsPlainToRecordPlain id.id_out history rg lastFrag in
                    let pv = pickSendPV (Conn(id,c)) in
                    let resSend = send c.ns id.id_out c.write pv rg Handshake frag in
                    match resSend with 
                          | Correct(new_write) ->
                            (* Also move to the Finished state *)
                            let c_write = {new_write with disp = Finished} in
                            let c = { c with handshake = new_hs_state;
                                             write     = c_write } in
                            (WriteFinished, Conn(id,c))
                          | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
                | _ -> (* Internal error: send a fatal alert to the other side *)
                        let reason = perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state" in
                        let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in (WriteAgainClosing, closing))
          | (Handshake.OutComplete(rg,lastFrag,new_hs_state)) ->
                (let c_read = c.read in
                match (c_write.disp, c_read.disp) with
                | (Finishing, Finished) ->
                    (* Send the last fragment *)
                    (let history = Record.history id.id_out Writer c_write.conn in
                    let ki = TLSInfo.mk_id id.id_out in
                    let es = HSFragment.init ki in
                    let hs = TLSFragment.handshakeHistory id.id_out history in
                    let lastFrag = HSFragment.reStream ki es rg lastFrag hs in
                    let frag = TLSFragment.hsPlainToRecordPlain id.id_out history rg lastFrag in
                    let pv = pickSendPV (Conn(id,c)) in
                    let resSend = send c.ns id.id_out c.write pv rg Handshake frag in
                    match resSend with 
                    | Correct(new_write) ->
                        let c = { c with handshake = new_hs_state;
                                         write     = new_write } in
                        (* Move to the new state *)
                        // Sanity check: in and out session infos should be the same
                        if epochSI(id.id_in) = epochSI(id.id_out) then
                            match moveToOpenState (Conn(id,c)) with
                            | Correct(c) -> (WHSDone,Conn(id,c))
                            | Error z ->
                                let (x,y) = z in
                                let closing = abortWithAlert (Conn(id,c)) AD_internal_error y in (WriteAgainClosing, closing)
                        else
                            let closed = closeConnection (Conn(id,c)) in
                            let reason = perror __SOURCE_FILE__ __LINE__ "Invalid connection state" in
                            (WError(reason),closed) (* Unrecoverable error *)
                    | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
                | _ -> (* Internal error: send a fatal alert to the other side *)
                        let reason = perror __SOURCE_FILE__ __LINE__ "Sending handshake message in wrong state" in
                        let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in (WriteAgainClosing, closing)))
      | (Alert.ALFrag(tlen,f),new_al_state) ->
        (match c_write.disp with
        | Init | FirstHandshake(_) | Open | Closing(_,_) ->
            (let history = Record.history id.id_out Writer c_write.conn in
            let ki = TLSInfo.mk_id id.id_out in
            let es = HSFragment.init ki in
            let hs = TLSFragment.alertHistory id.id_out history in
            let f = HSFragment.reStream ki es tlen f hs in
            let frag = TLSFragment.alertPlainToRecordPlain id.id_out history tlen f in
            let pv = pickSendPV (Conn(id,c)) in
            let c_write = c.write in
            let resSend = send c.ns id.id_out c_write pv tlen Alert frag in
            match resSend with 
            | Correct(new_write) ->
                let c = { c with alert   = new_al_state;
                                 write   = new_write } in
                (WriteAgain, Conn(id,c ))
            | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
        | _ ->
            let closed = closeConnection (Conn(id,c)) in
            let reason = perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state" in
            (WError(reason),closed)) (* Unrecoverable error *)
      | (Alert.LastALFrag(tlen,f,ad),new_al_state) ->
        (match c_write.disp with
        | Init | FirstHandshake(_) | Open | Closing(_,_) ->
            (* We're sending a fatal alert. Send it, then close both sending and receiving sides *)
            (let history = Record.history id.id_out Writer c_write.conn in
            let ki = TLSInfo.mk_id id.id_out in
            let es = HSFragment.init ki in
            let hs = TLSFragment.alertHistory id.id_out history in
            let f = HSFragment.reStream ki es tlen f hs in
            let frag = TLSFragment.alertPlainToRecordPlain id.id_out history tlen f in
            let pv = pickSendPV (Conn(id,c)) in
            let c_write = c.write in
            let resSend = send c.ns id.id_out c_write pv tlen Alert frag in
            match resSend with 
            | Correct(new_write) ->
                let c = {c with alert = new_al_state;
                                write = new_write} in
                let closed = closeConnection (Conn(id,c)) in
                let reason = getReason c_write.disp in
                (SentFatal(ad,reason), closed)
            | Error z -> let (x,y) = z in let closed = closeConnection (Conn(id,c)) in (WError(y),closed)) (* Unrecoverable error *)
        | _ ->
            let closed = closeConnection (Conn(id,c)) in
            let reason = perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state" in
            (WError(reason),closed)) (* Unrecoverable error *)
      | (Alert.LastALCloseFrag(tlen,f),new_al_state) -> 
        (match c_write.disp with
        | Init | FirstHandshake(_) | Open -> (* Not Closing: this is a graceful closure, should not happen in case of fatal alerts *)
            (* We're sending a close_notify alert. Send it, then only close our sending side.
               If we already received the other close notify, then reading is already closed,
               otherwise we wait to read it, then close. But do not close here. *)
            (let history = Record.history id.id_out Writer c_write.conn in
            let ki = TLSInfo.mk_id id.id_out in
            let es = HSFragment.init ki in
            let hs = TLSFragment.alertHistory id.id_out history in
            let f = HSFragment.reStream ki es tlen f hs in
            let frag = TLSFragment.alertPlainToRecordPlain id.id_out history tlen f in
            let pv = pickSendPV (Conn(id,c)) in
            let c_write = c.write in
            let resSend = send c.ns id.id_out c_write pv tlen Alert frag in
            match resSend with
            | Correct(new_write) ->
                let new_write = {new_write with disp = Closed} in 
                let c = {c with alert = new_al_state;
                                write = new_write} in
                (SentClose, Conn(id,c))
            | Error z -> 
                let (x,y) = z in
                let closed = closeConnection (Conn(id,c)) in 
                  (WError(y),closed)) (* Unrecoverable error *)
        | _ ->
            let closed = closeConnection (Conn(id,c)) in
            let reason = perror __SOURCE_FILE__ __LINE__ "Sending alert message in wrong state" in
            (WError(reason),closed)) (* Unrecoverable error *)

let rec writeAllClosing (Conn(id,s)) =
    match writeOne (Conn(id,s)) None with
    | (WriteAgain,c) -> writeAllClosing c
    | (WError(x),conn) -> WError(x),conn
    | (SentClose,conn) -> SentClose,conn
    | (SentFatal(x,y),conn) -> SentFatal(x,y),conn
    | (_,_) -> unexpected "[writeAllClosing] writeOne returned wrong result"

let rec writeAllFinishing conn =
    match writeOne conn None with
    | (WError(x),conn) -> (WError(x), conn)
    | (SentFatal(x,y),conn) -> (SentFatal(x,y),conn)
    | (SentClose,conn) -> (SentClose,conn)
    | (WriteAgainClosing, conn) -> writeAllClosing conn
    | (WriteAgain,conn) ->
        let (Conn(id,s)) = conn in
        writeAllFinishing (Conn(id,s))
    | (WriteFinished, conn) -> (WriteFinished, conn)
    | (WHSDone,conn) -> (WHSDone,conn)
    | (_,_) -> unexpected "[writeAllFinishing] writeOne returned wrong result"

let rec writeAllTop conn (ghost: option<(range * DataStream.delta * AppFragment.plain * DataStream.stream)>) =
    match writeOne conn ghost with
    | (WError(x),conn) -> (WError(x), conn)
    | (SentFatal(x,y),conn) -> (SentFatal(x,y),conn)
    | (SentClose,conn) -> (SentClose,conn)
    | (WriteAgainClosing,conn) -> writeAllClosing conn
    | (WDone,conn) -> (WDone,conn)
    | (WAppDataDone,conn) -> (WAppDataDone,conn)
    | (WriteAgainFinishing,conn) ->
        writeAllFinishing conn
    | (WriteAgain,conn) ->
        writeAllTop conn ghost
    | (_,_) -> unexpected "[writeAllTop] writeOne returned wrong result"

let getHeader (Conn(id,c)) =
    match Tcp.read c.ns 5 with // read & parse the header
    | Error x -> Error(AD_internal_error,x)
    | Correct header ->
        match Record.parseHeader header with
        | Error x -> Error(x)
        | Correct(res) ->
        let (ct,pv,len) = res in
        let c_read = c.read in
        match c_read.disp with
        | Init -> correct(ct,len)
        | FirstHandshake(expPV) ->
            if pv = expPV then
                correct(ct,len)
            else
                Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Protocol version check failed")
        | Finishing | Finished | Open ->
            let si = epochSI(id.id_in) in
            if pv = si.protocol_version then
                correct(ct,len)
            else
                Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Protocol version check failed")
        | _ -> unexpected "[recv] invoked on a closed connection"

let getFragment (Conn(id,c)) ct len =
    match Tcp.read c.ns len with
    | Error x -> Error(AD_internal_error,x)
    | Correct payload ->
        let c_read = c.read in
        let c_read_conn = c_read.conn in
        Record.recordPacketIn id.id_in c_read_conn ct payload

(* we have received, decrypted, and verified a record (ct,f); what to do? *)
let readOne (Conn(id,c0)) =
    let c_read = c0.read in
    match c_read.disp with
        | Closed ->
            let reason = perror __SOURCE_FILE__ __LINE__ "Trying to read from a closed connection" in
            let conn = (Conn(id,c0)) in
            let closing = abortWithAlert conn AD_internal_error reason in
            let wo,conn = writeAllClosing closing in
            WriteOutcome(wo),conn
        | _ ->
            match getHeader (Conn(id,c0)) with
            | Error z ->
                let (x,y) = z in
                let closing = abortWithAlert (Conn(id,c0)) x y in
                let wo,conn = writeAllClosing closing in
                WriteOutcome(wo),conn
            | Correct(received) -> 
                let (ct,len) = received in
                // prepare some variables for later use
                let history = Record.history id.id_in Reader c_read.conn in
                // The following pattern match
                // also checks the received ct is suitable for the current state
                match (ct,c_read.disp) with 
                | (Handshake, Init) | (Handshake, FirstHandshake(_)) | (Handshake, Finishing) | (Handshake, Open) ->
                    (match getFragment (Conn(id,c0)) ct len with
                    | Error z ->
                        let (x,y) = z in
                        let conn = (Conn(id,c0)) in
                        let closing = abortWithAlert conn x y in
                        let wo,conn = writeAllClosing closing in
                        WriteOutcome(wo),conn
                    | Correct recf ->
                        let (c_recv,rg,frag) = recf in
                        let c_read = {c_read with conn = c_recv} in
                        let c = {c0 with read = c_read} in
                        let c_hs = c.handshake in
                        let f = TLSFragment.recordPlainToHSPlain id.id_in history rg frag in
                        let hsRes = Handshake.recv_fragment id c_hs rg f in
                        
                    // AP: BEGIN: Inlined from handleHandshakeOutcome

                        match hsRes with
                        | Handshake.InAck(hs) ->
                            (let c = { c with handshake = hs} in
                            RAgain, Conn(id,c))
                        | Handshake.InVersionAgreed(hs,pv) ->
                            (match c_read.disp with
                            | Init ->
                                (* Then, also c_write must be in Init state. It means this is the very first, unprotected,
                                    handshake of the connection, and we just negotiated the version.
                                    Set the negotiated version in the current sinfo (read and write side), 
                                    and move to the FirstHandshake state, so that
                                    protocol version will be properly checked *)
                                let new_read = {c_read with disp = FirstHandshake(pv)} in
                                let c_write = c.write in
                                let new_write = {c_write with disp = FirstHandshake(pv)} in
                                let c = {c with handshake = hs;
                                                read = new_read;
                                                write = new_write} in
                                    (RAgain, Conn(id,c))
                            | _ -> (* It means we are doing a re-negotiation. Don't alter the current version number, because it
                                        is perfectly valid. It will be updated after the next CCS, along with all other session parameters *)
                                let c = { c with handshake = hs} in
                                    (RAgain, Conn(id, c)))
                        | Handshake.InQuery(query,advice,hs) ->
                                (let c = {c with handshake = hs} in
                                (RQuery(query,advice),Conn(id,c)))
                        | Handshake.InFinished(hs) ->
                                (* Ensure we are in Finishing state *)
                                (match c_read.disp with
                                    | Finishing ->
                                        let c_read = {c_read with disp = Finished} in
                                        let c = {c with handshake = hs;
                                                        read = c_read} in
                                        (RFinished,Conn(id,c))
                                    | _ ->
                                        let reason = perror __SOURCE_FILE__ __LINE__ "Finishing handshake in the wrong state" in
                                        let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in
                                        let wo,conn = writeAllClosing closing in
                                        WriteOutcome(wo),conn)
                        | Handshake.InComplete(hs) ->
                                (let c = {c with handshake = hs} in
                                (* Ensure we are in the correct state *)
                                let c_write = c.write in
                                match (c_read.disp, c_write.disp) with
                                | (Finishing, Finished) ->
                                    (* Sanity check: in and out session infos should be the same *)
                                    if epochSI(id.id_in) = epochSI(id.id_out) then
                                        match moveToOpenState (Conn(id,c)) with
                                        | Correct(c) -> 
                                            (RHSDone, Conn(id,c))
                                        | Error(z) -> 
                                            let (x,y) = z in
                                            let closing = abortWithAlert (Conn(id,c)) x y in
                                            let wo,conn = writeAllClosing closing in
                                            WriteOutcome(wo),conn
                                    else let closed = closeConnection (Conn(id,c)) in (RError(perror __SOURCE_FILE__ __LINE__ "Invalid connection state"),closed) (* Unrecoverable error *)
                                | _ ->
                                    let reason = perror __SOURCE_FILE__ __LINE__ "Invalid connection state" in
                                    let closing = abortWithAlert (Conn(id,c)) AD_internal_error reason in
                                    let wo,conn = writeAllClosing closing in
                                    WriteOutcome(wo),conn)
                        | Handshake.InError(x,y,hs) ->
                            (let c = {c with handshake = hs} in
                            let closing = abortWithAlert (Conn(id,c)) x y in
                            let wo,conn = writeAllClosing closing in
                            WriteOutcome(wo),conn))

                        // AP: END: Inlined from handleHandshakeOutcome

                  | (Change_cipher_spec, FirstHandshake(_)) | (Change_cipher_spec, Open) ->
                        (match getFragment (Conn(id,c0)) ct len with
                        | Error z ->
                            let (x,y) = z in
                            let conn = (Conn(id,c0)) in
                            let closing = abortWithAlert conn x y in
                            let wo,conn = writeAllClosing closing in
                            WriteOutcome(wo),conn
                        | Correct recf ->
                            let (c_recv,rg,frag) = recf in
                            let c_read = {c_read with conn = c_recv} in
                            let c = {c0 with read = c_read} in
                            let f = TLSFragment.recordPlainToCCSPlain id.id_in history rg frag in
                            match Handshake.recv_ccs id c.handshake rg f with 
                              //#begin-alertAttackRecv
                              | InCCSAck(nextID,nextR,hs) ->
                                  (* We know statically that Handshake and Application data buffers are empty.
                                   * We check Alert. We are going to reset the Alert buffer anyway, so we
                                   * never concatenate buffers of different epochs. But it is nicer to abort the
                                   * session if some buffers are not in the expected state. *)
                                  if Alert.is_incoming_empty id c.alert then
                                      let nextRCS = Record.initConnState nextID.id_in Reader nextR in
                                      let new_read = {c_read with disp = Finishing; conn = nextRCS} in
                                      let new_ad = AppData.reset_incoming id c.appdata nextID in
                                      let new_al = Alert.reset_incoming id c.alert nextID in
                                      let c = { c with read = new_read;
                                                       appdata = new_ad;
                                                       alert = new_al;
                                                       handshake = hs;
                                              } in
                                      (RAgainFinishing, Conn(nextID,c))
                                   else
                                      let reason = perror __SOURCE_FILE__ __LINE__ "Changing epoch with non-empty buffers" in
                                      let closing = abortWithAlert (Conn(id,c)) AD_handshake_failure reason in
                                      let wo,conn = writeAllClosing closing in
                                      WriteOutcome(wo),conn
                              //#end-alertAttackRecv
                              | InCCSError (x,y,hs) ->
                                  let c = {c with handshake = hs} in
                                  let closing = abortWithAlert (Conn(id,c)) x y in
                                  let wo,conn = writeAllClosing closing in
                                  WriteOutcome(wo),conn)

                  | (Alert, Init) | (Alert, FirstHandshake(_)) | (Alert, Open) ->
                        (match getFragment (Conn(id,c0)) ct len with
                        | Error z ->
                            let (x,y) = z in
                            let conn = (Conn(id,c0)) in
                            let closing = abortWithAlert conn x y in
                            let wo,conn = writeAllClosing closing in
                            WriteOutcome(wo),conn
                        | Correct recf ->
                            let (c_recv,rg,frag) = recf in
                            let c_read = {c_read with conn = c_recv} in
                            let c = {c0 with read = c_read} in
                            let f = TLSFragment.recordPlainToAlertPlain id.id_in history rg frag in
                            match Alert.recv_fragment id c.alert rg f with
                              | Correct (Alert.ALAck(state)) ->
                                  let c = {c with alert = state} in
                                  (RAgain, Conn(id,c))
                              | Correct (Alert.ALClose_notify (state)) ->
                                     (* An outgoing close notify has already been buffered, if necessary *)
                                     (* Only close the reading side of the connection *)
                                 let new_read = {c_read with disp = Closed} in
                                 let c = { c with read = new_read;
                                                  alert = state;
                                         } in
                                 (RClose, Conn(id,c))
                              | Correct (Alert.ALFatal (ad,state)) ->
                                   (* Other fatal alert, we close both sides of the connection *)
                                 let c = {c with alert = state} in
                                 let closed = closeConnection (Conn(id,c)) in
                                 (RFatal(ad), closed)
                              | Correct (Alert.ALWarning (ad,state)) ->
                                 (* A warning alert, we carry on. The user will decide what to do *)
                                 let c = {c with alert = state} in
                                 (RWarning(ad), Conn(id,c))
                              | Error z -> 
                                  let (x,y) = z in
                                  let closing = abortWithAlert (Conn(id,c)) x y in
                                  let wo,conn = writeAllClosing closing in
                                  WriteOutcome(wo),conn)

                  | Application_data, Open ->
                    (match getFragment (Conn(id,c0)) ct len with
                    | Error z ->
                        let (x,y) = z in
                        let conn = (Conn(id,c0)) in
                        let closing = abortWithAlert conn x y in
                        let wo,conn = writeAllClosing closing in
                        WriteOutcome(wo),conn
                    | Correct recf ->
                        let (c_recv,rg,frag) = recf in
                        let c_read = {c_read with conn = c_recv} in
                        let c = {c0 with read = c_read} in
                        let f = TLSFragment.recordPlainToAppPlain id.id_in history rg frag in
                        let (d,appstate) = AppData.recv_fragment id c.appdata rg f in
                        let c = {c with appdata = appstate} in
                        let res = (rg,d) in
                        (RAppDataDone(res), Conn(id, c)))
                  | _, Closed | _, Closing(_,_) | _, Finished | _, Finishing | _, Init
                  | _, FirstHandshake(_) ->
                      (let reason = perror __SOURCE_FILE__ __LINE__ "Message type received in wrong state" in
                      let closing = abortWithAlert (Conn(id,c0)) AD_unexpected_message reason in
                      let wo,conn = writeAllClosing closing in
                      WriteOutcome(wo),conn)

let sameID (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | RAgain -> RAgain
    | RAgainFinishing -> RAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | RQuery(x,y) -> RQuery(x,y)
    | RFinished -> RFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)

let sameID2 (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | RAgain -> RAgain
    | RAgainFinishing -> RAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | RQuery(x,y) -> RQuery(x,y)
    | RFinished -> RFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)

let sameIDRAF (c0:Connection) (c1:Connection) res (c2:Connection) =
    match res with
    | WriteOutcome(x) -> WriteOutcome(x)
    | RError(x) -> RError(x)
    | RAgain -> RAgain
    | RAgainFinishing -> RAgainFinishing
    | RAppDataDone(x) -> RAppDataDone(x)
    | RQuery(x,y) -> RQuery(x,y)
    | RFinished -> RFinished
    | RHSDone -> RHSDone
    | RClose -> RClose
    | RFatal(x) -> RFatal(x)
    | RWarning(x) -> RWarning(x)

let rec readAllFinishing c =
    let orig = c in
    let (outcome,c) = readOne c in
    match outcome with
    | RAgain ->
        (let (newConn,ro) = readAllFinishing c in
        let ro = sameIDRAF c newConn ro orig in
        newConn,ro)
    | RHSDone -> c,RHSDone
    | RFatal(ad) -> c,RFatal(ad)
    | RError(err) -> unexpected "[readAllFinishing] Read error can never be returned by read one"
    | RFinished ->
        (let (outcome,c) = writeAllTop c None in
        match outcome with
        | WHSDone -> c,WriteOutcome(WHSDone)
        | SentFatal(x,y) -> unexpected "[readAllFinishing] There should be no way of sending a fatal alert after we validated the peer Finished message"
        | WError(x) -> c,WriteOutcome(WError(x))
        | SentClose ->unexpected "[readAllFinishing] There should be no way of sending a closure alert after we validated the peer Finished message"
        | _ -> unexpected "[readAllFinishing] writeAllTop should never return such write outcome")
    | RAgainFinishing | RAppDataDone(_) | RQuery(_,_) -> unexpected "[readAllFinishing] readOne returned wrong result"
    | WriteOutcome(SentFatal(x,y)) -> c,WriteOutcome(SentFatal(x,y))
    | WriteOutcome(WError(x)) -> c,WriteOutcome(WError(x))
    | WriteOutcome(_) -> unexpected "[readAllFinishing] readOne should never return such write outcome"
    | WriteOutcome(SentClose)
        (* This and the following two corner cases are underspecified in RFC 5246, and we handle them by tearing down the connection.
           These are inconsistent states of the protocol that should be explicitly forbidden by the RFC.

           In this case, sending our CCS already implicitly closed the previous sending epoch, and the new epoch is not open
           yet, so there's nothing to close.
         *)
    | RClose
        (* This is the dual case of the above: we received the CCS, which implicitly closed the receiving epoch,
           and the new epoch is not open yet, so we cannot receive authenticated data, nor close this epoch.
         *)
    | RWarning(_) ->
        (* Like in the case above, the receiving epoch is closed, so we cannot accept authenticated data. *)
         let reason = perror __SOURCE_FILE__ __LINE__ "Trying to close an epoch after CCS has been sent, but before new epoch opened." in
         c,RError(reason)

let rec read c =
    let orig = c in
    let (outcome,c) = writeAllTop c None in
    match outcome with
    | SentClose -> c,WriteOutcome(SentClose)
    | SentFatal(ad,err) -> c,WriteOutcome(SentFatal(ad,err))
    | WError(err) -> c,WriteOutcome(WError(err))
    | WriteAgain | WriteAgainFinishing | WriteAgainClosing -> unexpected "[read] writeAllTop should never return WriteAgain"
    | WHSDone -> unexpected "[read] writeAllTop should never return handshake complete from read"
    | WAppDataDone -> unexpected "[read] writeAllTop should never send application data from read"
    | WriteFinished -> c,WriteOutcome(WriteFinished)
    | WDone -> (* There was nothing to write *)
        (let (outcome,c) = readOne c in
        match outcome with
        | RAgain ->
            (let (newConn,res) = read c in
            let res = sameID c newConn res orig in
            newConn,res)
        | RAgainFinishing ->
            (let (newConn,res) = readAllFinishing c in
            let res = sameID2 c newConn res orig in
            newConn,res)
        | RAppDataDone(msg) ->    
            c,RAppDataDone(msg)
        | RQuery(q,adv) ->
            c,RQuery(q,adv)
        | RHSDone | RFinished ->
            unexpected "[read] handshake should never complete without finishing first"
        | RClose ->
            (let (Conn(id,conn)) = c in
            match conn.write.disp with
            | Closed ->
                // we already sent a close_notify, tell the user it's over
                c,RClose
            | _ ->
                let (outcome,c) = writeAllClosing c in
                match outcome with
                | SentClose ->
                    // clean shoutdown
                    c,RClose
                | SentFatal(ad,err) ->
                    c,WriteOutcome(SentFatal(ad,err))
                | WError(err) ->
                    c,RError(err)
                | _ ->
                    c,RError(perror __SOURCE_FILE__ __LINE__ "")) // internal error
        | RFatal(ad) ->
            c,RFatal(ad)
        | RWarning(ad) ->
            c,RWarning(ad)
        | WriteOutcome(SentFatal(x,y)) -> c,WriteOutcome(SentFatal(x,y))
        | WriteOutcome(WError(x)) -> c,WriteOutcome(WError(x))
        | WriteOutcome(SentClose) -> c,WriteOutcome(SentClose)
        | WriteOutcome(_) -> unexpected "[read] readOne should never return such write outcome"
        | RError(err) -> c,RError(err))

let write (Conn(id,s)) (rg,d) =
  let outStr = AppData.outStream id s.appdata in
  let (f,ns) = AppFragment.mk_fragment id.id_out outStr rg d in
  let new_appdata = AppData.writeAppData id s.appdata rg f ns in
  let s = {s with appdata = new_appdata} in
  let ghost = (rg,d,f,ns) in
  let ghost = Some(ghost) in
  let (outcome,Conn(id,s)) = writeAllTop (Conn(id,s)) ghost in
  let new_appdata = AppData.clearOutBuf id s.appdata in
  let s = {s with appdata = new_appdata} in
  match outcome with //AP: prune some options
  | WError (_) | SentFatal(_,_) -> Conn(id,s),outcome
  | WriteFinished -> Conn(id,s),outcome
  | WAppDataDone -> Conn(id,s),outcome
  | WriteAgain | WriteAgainFinishing | WriteAgainClosing
  | WDone | WHSDone | SentClose ->
    unexpected "[write] writeAllTop should never return this"

let authorize (Conn(id,c)) q =
    let hsRes = Handshake.authorize id c.handshake q in
    let c_read = c.read in

    // AP: BEGIN: Inlined from handleHandshakeOutcome

    match hsRes with
    | Handshake.InAck(hs) ->
        (let c1 = { c with handshake = hs} in
        let (newConn,res) = read (Conn(id,c1)) in
        let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in
        (newConn,res))
    | Handshake.InVersionAgreed(hs,pv) ->
        (match c_read.disp with
        | Init ->
            (* Then, also c_write must be in Init state. It means this is the very first, unprotected,
                handshake on the connection, and we just negotiated the version.
                Set the negotiated version in the current sinfo (read and write side), 
                and move to the FirstHandshake state, so that
                protocol version will be properly checked *)
            let new_read = {c_read with disp = FirstHandshake(pv)} in
            let c_write = c.write in
            let new_write = {c_write with disp = FirstHandshake(pv)} in
            let c1 = {c with handshake = hs;
                            read = new_read;
                            write = new_write} in
            let (newConn,res) = read (Conn(id,c1)) in
            let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in
            (newConn,res)
        | _ -> (* It means we are doing a re-negotiation. Don't alter the current version number, because it
                    is perfectly valid. It will be updated after the next CCS, along with all other session parameters *)
            let c1 = { c with handshake = hs} in
            let (newConn,res) = read (Conn(id,c1)) in
            let res = sameID (Conn(id,c1)) newConn res (Conn(id,c)) in
            (newConn,res))
    | Handshake.InQuery(query,advice,hs) ->
        unexpected "[authorize] A query should never be received"
    | Handshake.InFinished(hs) ->
        unexpected "[authorize] The finished message should never be received right after a query"
    | Handshake.InComplete(hs) ->
        unexpected "[authorize] Handshake should never complete right after a query"
    | Handshake.InError(x,y,hs) ->
        (let c = {c with handshake = hs} in
        let closing = abortWithAlert (Conn(id,c)) x y in
        let wo,conn = writeAllClosing closing in
        conn,WriteOutcome(wo))

    // AP: END: Inlined from handleHandshakeOutcome

let refuse conn (q:query) =
    let reason = perror __SOURCE_FILE__ __LINE__ "Remote certificate could not be verified locally" in
    let conn = abortWithAlert conn AD_unknown_ca reason in
    let _ = writeAllClosing conn in
    ()

let full_shutdown (Conn(id,conn)) =
    let new_al = Alert.send_alert id conn.alert AD_close_notify in
    let conn = {conn with alert = new_al} in
    Conn(id,conn)

let half_shutdown (Conn(id,conn)) =
    let new_al = Alert.send_alert id conn.alert AD_close_notify in
    let conn = {conn with alert = new_al} in
    let _ = writeAllClosing (Conn(id,conn)) in
    ()

let getEpochIn  (Conn(id,state)) = id.id_in
let getEpochOut (Conn(id,state)) = id.id_out
let getInStream  (Conn(id,state)) = AppData.inStream  id state.appdata
let getOutStream (Conn(id,state)) = AppData.outStream id state.appdata 
