module TLS.Result 

(* TLS explicitly returns run-time errors:
   results carry either values or error descriptions *)

// only for their datatypes
include Parsers.AlertDescription


// rewritten for lowering and nicer extraction, was [alert * string]
type error = { alert: alertDescription; cause: string } 

// this module will often be opened, for pattern-matching on results
type result 'a =
  | Correct of 'a
  | Error of error
// used to be specialized from FStar.Error

// not inlined (in source C) for readability
let correct (x:'a): result 'a = Correct x
let fail #a z: result a = Error z

let alert = Parsers.Alert.alert
val string_of_alert: alert -> string 
val fatalAlert: alertDescription -> alert

val string_of_error: error -> string
val string_of_result: #a:_ ->  (a -> string) -> result a -> string 

// not inlined (in source C) for readability
let fatal #a (ad:alertDescription) (s:string): result a = Error ({alert=ad; cause=norm [primops] s})

val resT: r:result 'a { Correct? r } -> 'a

inline_for_extraction
val mapResult: ('a -> 'b) -> result 'a -> result 'b
val bindResult: ('a -> result 'b) -> result 'a -> result 'b
val resultMap: result 'a -> ('a -> Tot 'b) -> result 'b
val resultBind: result 'a -> ('a -> result 'b) -> result 'b

(* connecting with LowParse, which uses option *)

let option_of_result (r: result 'a): option 'a =
  match r with
  | Error _ -> None
  | Correct c -> Some c

(* lightweight error handling? *) 

inline_for_extraction
let bind (#a:Type) (#b:Type)
         (f: result a)
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
// compiles to "TLS.Result.fst:123 test error"


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
  (p:bool)
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
let lift_div_tlsexn (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> DIV a wp)
: exn_repr a (fun p h -> wp (fun x -> p (Correct x) h))
= fun _ ->
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  Correct (f ())

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
