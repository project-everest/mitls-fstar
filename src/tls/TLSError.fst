module TLSError
open FStar.String
(* TLS explicitly returns run-time errors:
   results carry either values or error descriptions *)

include FStar.Error // avoids double-include in other modules, and prepares its elimination.

include Parsers.AlertDescription
include Parsers.AlertLevel
include Parsers.Alert

let string_of_alert (a:alert) = 
  "level="^string_of_alertLevel a.level^
  ", description="^string_of_alertDescription a.description

let fatalAlert ad = {level=Fatal; description=ad}

(* TODO functions checking consistency of levels and descriptions *)

// let isFatal ad =
//     match ad with
//     | AD_unexpected_message
//     | AD_bad_record_mac
//     | AD_decryption_failed
//     | AD_record_overflow
//     | AD_decompression_failure
//     | AD_handshake_failure
//     | AD_bad_certificate_fatal
//     | AD_unsupported_certificate_fatal
//     | AD_certificate_revoked_fatal
//     | AD_certificate_expired_fatal
//     | AD_certificate_unknown_fatal
//     | AD_illegal_parameter
//     | AD_unknown_ca
//     | AD_access_denied
//     | AD_decode_error
//     | AD_decrypt_error
//     | AD_export_restriction
//     | AD_protocol_version
//     | AD_insufficient_security
//     | AD_internal_error
//     | AD_user_cancelled_fatal
//     | AD_missing_extension
//     | AD_unsupported_extension
//     | AD_no_application_protocol -> true
//     | _ -> false

// rewritten for lowering and nicer extraction, was [alert * string]
type error = { alert: alertDescription; cause: string } 

let string_of_error (e:error) = FStar.Printf.sprintf "%s: %s" (string_of_alertDescription e.alert) e.cause

type result 'a = FStar.Error.optResult error 'a

open FStar.Error
let string_of_result f = function
  | Error z -> "Error: "^string_of_error z
  | Correct v -> f v

// not inlined (in source C) for readability
let fatal #t a s: result t = Error ({alert=a; cause=norm [primops] s})

val resT: r:result 'a { FStar.Error.Correct? r } -> Tot 'a
let resT (FStar.Error.Correct v) = v

inline_for_extraction
val mapResult: ('a -> Tot 'b) -> result 'a -> Tot (result 'b)
inline_for_extraction
let mapResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val bindResult: ('a -> Tot (result 'b)) -> result 'a -> Tot (result 'b)
let bindResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

val resultMap: result 'a -> ('a -> Tot 'b) -> Tot (result 'b)
let resultMap r f =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val resultBind: result 'a -> ('a -> Tot (result 'b)) -> Tot (result 'b)
let resultBind r f =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

(* connecting with LowParse, which uses option *)

let option_of_result (#t: Type) (r: result t) : Tot (option t) =
  match r with
  | Error _ -> None
  | Correct c -> Some c


(* lightweight error handling? *) 

// masking the polymorphic one in FStar.Error

// not inlined (in source C) for readability
let correct #t x: result t = Correct x
let fail #t z: result t = Error z

inline_for_extraction
let bind (#a:Type) (#b:Type)
         (f:result a)
         (g: a -> result b)
    : result b
    = match f with
      | Correct x -> g x
      | Error z -> Error z

inline_for_extraction noextract 
let perror
    (file:string)
    (line:int)
    (text:string)
  :  string
  = normalize_term (Printf.sprintf "%s:%d %s" file line text)

// let perror_unit_test = perror __SOURCE_FILE__ __LINE__ "test error"
// compiles to "TLSError.fst:123 test error"


(*** A layered exception effect over HST ***)


open FStar.HyperStack.ST

module HS = FStar.HyperStack

/// Type of preconditions, postconditions, and wp
///
/// We are assuming monotonicity as an axiom FOR NOW
/// It should be possible to make it a refinement in the type of exn_wp_t
///   But currently `exn_bind` proof fails with that, should look into it

type exn_pre_t = HS.mem -> Type0
type exn_post_t (a:Type) = result a -> HS.mem -> Type0
type exn_wp_t (a:Type) = exn_post_t a -> exn_pre_t


assume WP_exn_monotonic :
  forall (a:Type) (wp:exn_wp_t a).
    (forall p q. (forall r h. p r h ==> q r h) ==> (forall h. wp p h ==> wp q h))


/// Layered effect combinators

type exn_repr (a:Type) (wp:exn_wp_t a) = unit -> STATE (result a) wp


inline_for_extraction
let exn_return (a:Type) (x:a)
: exn_repr a (fun p h -> p (Correct x) h)
= fun _ -> Correct x


inline_for_extraction
let exn_bind (a:Type) (b:Type)
  (wp_f:exn_wp_t a) (wp_g:a -> exn_wp_t b)
  (f:exn_repr a wp_f) (g:(x:a -> exn_repr b (wp_g x)))
: exn_repr b
  (fun p h0 ->
    wp_f (fun x h1 ->
      match x with
      | Error e -> p (Error e) h1
      | Correct x -> (wp_g x) p h1) h0)
= fun _ ->
  let r = f () in
  match r with
  | Error e -> Error e
  | Correct x -> (g x) ()


inline_for_extraction
let exn_subcomp (a:Type)
  (wp_f:exn_wp_t a) (wp_g:exn_wp_t a)
  (f:exn_repr a wp_f)
: Pure (exn_repr a wp_g)
  (requires forall p h. wp_g p h ==> wp_f p h)
  (ensures fun _ -> True)
= f


inline_for_extraction
let exn_if_then_else (a:Type)
  (wp_then:exn_wp_t a) (wp_else:exn_wp_t a)
  (f:exn_repr a wp_then) (g:exn_repr a wp_else)
  (p:Type0)
: Type
= exn_repr a (fun post h ->
    (p ==> wp_then post h) /\
    ((~ p) ==> wp_else post h))


/// The effect definition
///
/// The name is a mouthful here, but clients will rarely use this form
///   Mostly they will use the derived forms below

reifiable reflectable
layered_effect {
  TLSEXN : a:Type -> wp:exn_wp_t a -> Effect
  with
  repr = exn_repr;
  return = exn_return;
  bind = exn_bind;
  subcomp = exn_subcomp;
  if_then_else = exn_if_then_else
}


/// Lift from DIV to TLSSTATEEXN

inline_for_extraction
let lift_div_tlsexn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: exn_repr a (fun p h -> wp (fun x -> p (Correct x) h))
= fun _ -> Correct (f ())

sub_effect DIV ~> TLSEXN = lift_div_tlsexn


/// Effect abbreviations
///
/// The general definition of the effect does not say anything about the heap domains
///   e.g. it does not mention `equal_stack_domains` or `equal_domains` etc.
///
/// The following derived forms capture these


effect TLSExn (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> result a -> HS.mem -> Type0) =
  TLSEXN a (fun p h0 -> pre h0 /\ (forall r h1. post h0 r h1 ==> p r h1))

effect TLSSTExn (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> result a -> HS.mem -> Type0) =
  TLSEXN a (fun p h0 -> pre h0 /\ (forall r h1. (equal_stack_domains h0 h1 /\ post h0 r h1) ==> p r h1))

effect TLSStackExn (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> result a -> HS.mem -> Type0) =
  TLSEXN a (fun p h0 -> pre h0 /\ (forall r h1. (equal_domains h0 h1 /\ post h0 r h1) ==> p r h1))
