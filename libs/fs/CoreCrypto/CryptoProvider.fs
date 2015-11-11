(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* ------------------------------------------------------------------------ *)
namespace CryptoProvider

open System
open System.Reflection

(* ------------------------------------------------------------------------ *)
type key   = byte[]
type iv    = byte[]
type adata = byte[]

(* ------------------------------------------------------------------------ *)
type MessageDigest =
    interface
        abstract Name   : string
        abstract Digest : byte[] -> byte[]
    end

(* ------------------------------------------------------------------------ *)
type direction = ForEncryption | ForDecryption
type cipher    = AES | DES3
type mode      = CBC of iv

type BlockCipher =
    interface
        abstract Name      : string
        abstract Direction : direction
        abstract BlockSize : int
        abstract Process   : byte[] -> byte[]
    end

(* ------------------------------------------------------------------------ *)
type acipher = AES
type amode   = GCM of iv * adata

type AeadCipher =
    interface
        abstract Name      : string
        abstract Direction : direction
        abstract Process   : byte[] -> byte[]
    end

(* ------------------------------------------------------------------------ *)
type scipher = RC4

type StreamCipher =
    interface
        abstract Name      : string
        abstract Direction : direction
        abstract Process   : byte[] -> byte[]
    end

(* ------------------------------------------------------------------------ *)
type HMac =
    interface
        abstract Name    : string
        abstract Process : byte[] -> byte[]
    end

(* ------------------------------------------------------------------------ *)
type Provider =
    interface
        abstract MessageDigest :
            string -> MessageDigest option

        abstract AeadCipher :
            direction -> acipher -> amode -> key -> AeadCipher option

        abstract BlockCipher :
            direction -> cipher -> mode option -> key -> BlockCipher option

        abstract StreamCipher :
            direction -> scipher -> key -> StreamCipher option

        abstract HMac :
            string -> key -> HMac option
    end

(* ------------------------------------------------------------------------ *)
exception CannotLoadProvider of string
exception NoMessageDigest    of string
exception NoBlockCipher      of cipher * mode option
exception NoAeadCipher       of acipher * amode
exception NoStreamCipher     of scipher
exception NoHMac             of string
exception AEADFailure

type CoreCrypto () =
    static let default_provider = "BCCryptoProvider.BCProvider"

    static let mutable providers   = ref []
    static let mutable initialized = ref false
    static let mutable config      = ref CoreCrypto.Config

    static member Register (provider : Provider) =
        providers := !providers @ [provider]

    static member Providers =
        Array.ofList !providers

    static member Digest (name : string) =
        !config ();
        let select (p : Provider) = p.MessageDigest name in
            match !providers |> List.tryPick select with
            | None   -> raise (NoMessageDigest name)
            | Some x -> x

    static member AeadCipher (d : direction) (c : acipher) (m : amode) (k : key) =
        !config ();
        let select (p : Provider) = p.AeadCipher d c m k in
            match !providers |> List.tryPick select with
            | None   -> raise (NoAeadCipher (c, m))
            | Some x -> x

    static member BlockCipher (d : direction) (c : cipher) (m : mode option) (k : key) =
        !config ();
        let select (p : Provider) = p.BlockCipher d c m k in
            match !providers |> List.tryPick select with
            | None   -> raise (NoBlockCipher (c, m))
            | Some x -> x

    static member StreamCipher (d : direction) (c : scipher) (k : key) =
        !config ();
        let select (p : Provider) = p.StreamCipher d c k in
            match !providers |> List.tryPick select with
            | None   -> raise (NoStreamCipher c)
            | Some x -> x

    static member HMac (name : string) (k : key) =
        !config ();
        let select (p : Provider) = p.HMac name k in
            match !providers |> List.tryPick select with
            | None   -> raise (NoHMac name)
            | Some x -> x

    static member LoadProvider (name : string) =
        !config ()
        let type_ = Type.GetType (name) in
        if type_ = null || not type_.IsClass then
            raise (CannotLoadProvider name);
        if not (typeof<Provider>.IsAssignableFrom (type_)) then
            raise (CannotLoadProvider name);
        let provider =
            try
                Activator.CreateInstance(type_) :?> Provider
            with
            | :? SystemException
            | :? ApplicationException ->  raise (CannotLoadProvider name)  
        in
            CoreCrypto.Register provider; provider

    static member Config () =
        let doit () =
            let providers = Environment.GetEnvironmentVariable("mitls_crypto_provider") in
            let providers = if providers = null then default_provider else providers in
            let providers = providers.Split([| ':' |]) in

            let register1 (name : string) =
                try
                    ignore (CoreCrypto.LoadProvider (name))
                with CannotLoadProvider _ ->
#if DEBUG
                    fprintfn stderr "cannot load crypto provider `%s'" name
#else
                    ()
#endif
            in
                Array.iter register1 providers
        in
            lock initialized (fun () ->
                config := (fun () -> ());
                if not !initialized then doit ();
                initialized := true)

