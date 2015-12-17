(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.FlexHandshake


open NLog

open Bytes
open Error
open TLSConstants

open FlexTypes
open FlexConstants
open FlexState
open FlexRecord

/// <summary>
/// Module receiving, sending and forwarding TLS handshake messages.
/// </summary>
type FlexHandshake =
    class

    /// <summary>
    /// Parse a Handshake message from a buffer and leave the remaining data in the buffer
    /// </summary>
    /// <param name="buf"> Buffer containing handshake message(s) </param>
    /// <returns> PreHandshakeType * payload * full message * remainder of the buffer </returns>
    static member parseHSMessage (buf:bytes) =
        if length buf >= 4 then
            let (hstypeb,rem) = Bytes.split buf 1 in
            match HandshakeMessages.parseHt hstypeb with
            | Error (_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
            | Correct(hst) ->
                let (lenb,rem) = Bytes.split rem 3 in
                let len = int_of_bytes lenb in
                if length rem < len then
                    Error("Given buffer too small")
                else
                    let (payload,rem) = Bytes.split rem len in
                    let to_log = hstypeb @| lenb @| payload in
                    Correct (hst,payload,to_log,rem)
        else
            Error("Given buffer too small")

    /// <summary>
    /// Get an Handshake message from a network stream and manage buffering
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <returns> Updated state * PreHandshakeType * payload * full message * remainder of the buffer </returns>
    static member receive (st:state) : state * HandshakeMessages.PreHandshakeType * bytes * bytes =
        let buf = st.read.hs_buffer in
        match FlexHandshake.parseHSMessage buf with
        | Error(_) ->
            (let ct,pv,len,_ = FlexRecord.parseFragmentHeader st in
            match ct with
            | Handshake ->
                let st,b = FlexRecord.getFragmentContent (st, ct, len) in
                let buf = buf @| b in
                let st = FlexState.updateIncomingHSBuffer st buf in
                FlexHandshake.receive st
            | _ ->
                let _,b = FlexRecord.getFragmentContent (st, ct, len) in
                failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected content type : %A\n Payload (%d Bytes) : %s" ct len (Bytes.hexString(b)))))
        | Correct(hst,payload,to_log,rem) ->
                let st = FlexState.updateIncomingHSBuffer st rem in
                (st,hst,payload,to_log)

    /// <summary>
    /// Forward an Handshake message from a network stream without buffering anything
    /// </summary>
    /// <param name="stin"> State of the current Handshake on the incoming side </param>
    /// <param name="stout"> State of the current Handshake on the outgoing side </param>
    /// <param name="fp"> Optional fragmentation policy applied to the message </param>
    /// <returns> Updated incoming state * Updated outgoing state * forwarded handshake message bytes </returns>
    static member forward (stin:state, stout:state) : state * state * bytes =
        let stin,_,_,msg = FlexHandshake.receive(stin) in
        let stout = FlexHandshake.send(stout,msg) in
        stin,stout,msg

    /// <summary>
    /// Send an Handshake message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="payload"> Optional Data bytes to send as en handshake message. None will send the handshake buffer </param>
    /// <param name="fp"> Optional fragmentation policy applied to the message </param>
    /// <returns> Updated state </returns>
    static member send (st:state, ?payload:bytes, ?fp:fragmentationPolicy) : state =
        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
        let payload = defaultArg payload empty_bytes in
        let buf = st.write.hs_buffer @| payload in
        let st = FlexState.updateOutgoingHSBuffer st buf in
        LogManager.GetLogger("file").Debug(sprintf "--- Payload : %A" (Bytes.hexString(payload)));
        FlexRecord.send(st,Handshake,fp)

    end
