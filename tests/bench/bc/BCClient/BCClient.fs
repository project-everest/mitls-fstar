(* ------------------------------------------------------------------------ *)
open System
open System.Reflection
open System.Net
open System.Net.Sockets

open Org.BouncyCastle.Crypto.Prng
open Org.BouncyCastle.Crypto.Tls

(* ------------------------------------------------------------------------ *)
let block = 256 * 1024

(* ------------------------------------------------------------------------ *)
exception NotAValidEnumeration

let enumeration<'T> () =
    let t = typeof<'T>

    if not t.IsEnum then
        raise NotAValidEnumeration;

    let fields = t.GetFields (BindingFlags.Public ||| BindingFlags.Static) in
        Array.map   
            (fun (fi : FieldInfo) -> (fi.Name, fi.GetValue(null) :?> 'T))
            fields

(* ------------------------------------------------------------------------ *)
let cs_map = Map.ofArray (enumeration<CipherSuite> ())

(* ------------------------------------------------------------------------ *)
let udata = Array.create (1024*1024) 0uy

let initialize_udata () =
    let rnd = new CryptoApiRandomGenerator() in
        rnd.NextBytes(udata, 0, udata.Length)

(* ------------------------------------------------------------------------ *)
type MyAuthentication () =
    interface TlsAuthentication with
        member self.NotifyServerCertificate (_ : Certificate) =
            ()

        member self.GetClientCredentials (_ : CertificateRequest) =
            null

(* ------------------------------------------------------------------------ *)
type MyTlsClient (cs : CipherSuite) =
    inherit DefaultTlsClient ()

    override this.GetCipherSuites() =
        [|cs|]

    override this.GetAuthentication () =
        new MyAuthentication () :> TlsAuthentication

    override this.GetCompressionMethods () =
        [| CompressionMethod.NULL |]

(* ------------------------------------------------------------------------ *)
let client () =
    let cs = Environment.GetEnvironmentVariable("CIPHERSUITE") in
    let cs = Map.find cs cs_map in

    let hsdone  = ref 0 in
    let hsticks = ref (int64 (0)) in

    for i = 0 to 20 do
        use socket = new TcpClient ()
        socket.Connect (IPAddress.Loopback, 5000)

        let t1 = DateTime.Now.Ticks in
        let tlssock = new TlsProtocolHandler(socket.GetStream ())

        tlssock.Connect (new MyTlsClient (cs));
        tlssock.Stream.Write([| 0uy |], 0, 1);

        if i <> 0 then begin
            hsdone  := !hsdone  + 1;
            hsticks := !hsticks + (DateTime.Now.Ticks - t1);
        end

        tlssock.Close ();
    done;
    
    use socket = new TcpClient ()
    socket.Connect (IPAddress.Loopback, 5000)

    let tlssock = new TlsProtocolHandler(socket.GetStream ())
    tlssock.Connect (new MyTlsClient (cs))

    let sent  = ref 0 in
    let upos  = ref 0 in
    let ticks = DateTime.Now.Ticks in

        while !sent < 128*1024*1024 do
            if udata.Length - !upos < block then begin
                upos := 0
            end;
            tlssock.Stream.Write (udata, !upos, block)
            sent := !sent + block;
            upos := !upos + block;
        done;
        tlssock.Close ();

        let ticks = DateTime.Now.Ticks - ticks in
             ((!sent, ticks), (!hsdone, !hsticks))

(* ------------------------------------------------------------------------ *)
let program () =
    let cs = Environment.GetEnvironmentVariable("CIPHERSUITE") in

    initialize_udata ()

    let ((sent, ticks), (hsdone, hsticks)) = client () in
    let rate = float(sent) / (float(ticks) / float(TimeSpan.TicksPerSecond)) in
    let hsrate = float(hsdone) / (float(hsticks) / float(TimeSpan.TicksPerSecond)) in
        printfn "%s: %.2f HS/s" cs hsrate;
        printfn "%s: %.2f MiB/s" cs (rate / (1024. * 1024.))

(* ------------------------------------------------------------------------ *)
let _ = program ()
