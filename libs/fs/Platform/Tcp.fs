(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Tcp

open System.Net
open System.Net.Sockets
open Bytes
open Error

type NetworkStream = N of System.IO.Stream
type TcpListener = T of System.Net.Sockets.TcpListener

let create s = N(s)
let getStream (N(s)) = s

(* Server side *)

let listen addr port =
    let tcpList = new System.Net.Sockets.TcpListener(IPAddress.Parse(addr),port) in
    tcpList.Server.SetSocketOption(SocketOptionLevel.Socket, SocketOptionName.ReuseAddress, true);
    tcpList.Start();
    T tcpList

let acceptTimeout timeout (T tcpList) =
    let client = tcpList.AcceptTcpClient() in
    client.ReceiveTimeout <- timeout;
    client.SendTimeout <- timeout;
    N (client.GetStream())

let accept t =
    acceptTimeout 0 t

let stop (T tcpList) =
    tcpList.Stop()

(* Client side *)

let connectTimeout timeout addr port =
    let tcpCl = new TcpClient(addr,port) in
    tcpCl.ReceiveTimeout <- timeout;
    tcpCl.SendTimeout <- timeout;
    N (tcpCl.GetStream())

let connect addr port =
    connectTimeout 0 addr port

(* Input/Output *)

let rec read_acc (N ns) nbytes prev =
    if nbytes = 0 then
        Correct (abytes prev)
    else
        try
            let buf = Array.zeroCreate nbytes in
            let read = ns.Read (buf, 0, nbytes) in
            if read = 0 then
                Error(perror __SOURCE_FILE__ __LINE__ "TCP connection closed: Read returned 0 bytes")
            else
                let rem = nbytes - read in
                read_acc (N ns) rem (Array.append prev (Array.sub buf 0 read))
        with
            | e -> Error(perror __SOURCE_FILE__ __LINE__ ("TCP connection closed: "^ (e.ToString())))

let read (N ns) nbytes =
    try
        (read_acc (N ns) nbytes (Array.zeroCreate 0))
    with
        | e -> Error(perror __SOURCE_FILE__ __LINE__ ("TCP connection closed: "^ (e.ToString())))


let write (N ns) content =
    try
        let content = cbytes content in
        Correct (ns.Write (content, 0, content.Length))
    with
        | e -> Error(perror __SOURCE_FILE__ __LINE__ ("TCP connection closed: "^ (e.ToString())))

let close (N ns) =
    ns.Close()

