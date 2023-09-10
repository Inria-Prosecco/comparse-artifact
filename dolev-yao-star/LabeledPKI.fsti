/// LabeledPKI
/// ===========
///
/// This module provides a layer on top of :doc:`LabeledRuntimeAPI`, adding convenient ways to
/// handle public key infrastructure, e.g., generation and distribution of key pairs.  Note that
/// library clients should not mix stateful functions from :doc:`LabeledRuntimeAPI` with those
/// defined here - while this is technically possible, it may result in unexpected (but still
/// sound) behavior.
///
/// .. _labeledpki_layering_description:
///
/// Layering in DY*
/// ---------------
///
/// DY* is not only modular in terms of verification, but also in terms of the model itself: One can
/// add (derived) functionality in layers on top of the base model.  These layers may, for example,
/// add a more convenient way to handle asymmetric key pairs, or add request/response channels with
/// various channel properties.  On a technical level, layers usually "overwrite" and/or add
/// functions to the :doc:`LabeledRuntimeAPI` (with the implementation of these functions usually
/// using the corresponding functions from :doc:`LabeledRuntimeAPI`).  In addition to the functions,
/// layers usually also extend the trace invariants in some way (e.g., to provide guarantees for an
/// authenticated channel).
///
/// The convention for the latter is to define a function which maps ``preds`` (see
/// :ref:`LabeledRuntimeAPI <labeledruntimeapi_preds_definition>`) to ``preds``, e.g., for this
/// module, the function is called ``pki`` and the stateful functions in this module use ``pki
/// some_preds`` instead of just ``some_preds``.
module LabeledPKI

open SecrecyLabels
open CryptoEffect
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

/// Map general ``preds`` to PKI ``preds``.  The refinement exposes that usages and the event
/// predicate are not changed by the PKI layer.
val pki: pr:R.preds -> pr':R.preds{
    pr.R.global_usage == pr'.R.global_usage /\
    pr.R.trace_preds.R.can_trigger_event == pr'.R.trace_preds.R.can_trigger_event}

/// Stateful session API for PKI layer
/// ----------------------------------
let new_session_number (#pr:R.preds) (p:principal) :
  R.LCrypto nat (pki pr)
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0) =
  R.new_session_number #(pki pr) p

val new_session: #pr:R.preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
  R.LCrypto unit (pki pr)
  (requires fun t0 -> trace_len t0 == i /\ pr.R.trace_preds.R.session_st_inv i p si vi st)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val update_session: #pr:R.preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
  R.LCrypto unit (pki pr)
  (requires fun t0 -> trace_len t0 == i /\ pr.R.trace_preds.R.session_st_inv i p si vi st)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val get_session: #pr:R.preds -> #i:timestamp -> p:principal -> si:nat ->
  R.LCrypto (vi:nat & A.msg pr.R.global_usage i (readers [V p si vi])) (pki pr)
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 (|vi,st|) t1 -> t1 == t0 /\
                               pr.R.trace_preds.R.session_st_inv i p si vi st)

val find_session:
  #pr:R.preds -> #i:timestamp -> p:principal -> f:(si:nat -> vi:nat -> st:bytes -> bool) ->
  R.LCrypto (option (si:nat & vi:nat & A.msg pr.R.global_usage i (readers [V p si vi]))) (pki pr)
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 r t1 -> t1 == t0 /\
                       (match r with
                        | None -> True
                        | Some (|si,vi,st|) -> f si vi st /\
                                              pr.R.trace_preds.R.session_st_inv i p si vi st))


/// PKI-specific (stateful) APIs
/// ----------------------------

type key_type = | PKE | DH | SIG | OneTimeDH

let private_key (pr:R.preds) (i:timestamp) (si:nat) (p:principal) (kt:key_type) (t:string) =
  match kt with
  | PKE -> A.private_dec_key pr.R.global_usage i (readers [P p]) t
  | DH -> A.dh_private_key pr.R.global_usage i (readers [P p]) t
  | SIG -> A.sign_key pr.R.global_usage i (readers [P p]) t
  | OneTimeDH -> A.dh_private_key pr.R.global_usage i (readers [V p si 0]) t

let public_key (pr:R.preds) (i:timestamp) (p:principal) (kt:key_type) (t:string) =
  match kt with
  | PKE -> A.public_enc_key pr.R.global_usage i (readers [P p]) t
  | DH -> A.dh_public_key pr.R.global_usage i (readers [P p]) t
  | SIG -> A.verify_key pr.R.global_usage i (readers [P p]) t
  | OneTimeDH -> bytes

// Returns session index (of the session which stores the private key)
val gen_private_key: #pr:R.preds -> #i:timestamp -> p:principal -> kt:key_type -> t:string ->
    R.LCrypto (priv_key_session_id:nat) (pki pr)
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 = trace_len t0 + 2))

// Retrieve a private key for p, identified by its type and usage string. Returns the session index
// of the session in which the private key is stored, and of course the key itself.
val get_private_key: #pr:R.preds -> #i:timestamp -> p:principal -> kt:key_type -> t:string ->
    R.LCrypto (si:nat & private_key pr i si p kt t) (pki pr)
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> t0 == t1))

// Install public key of p (identified by type and usage string) at peer. Returns the session index
// at which the public key is stored in peer's state.
val install_public_key: #pr:R.preds -> #i:timestamp -> p:principal -> peer:principal -> kt:key_type -> t:string ->
    R.LCrypto nat (pki pr)
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 = trace_len t0 + 1))

// Retrieve the public key or peer (identified by type and usage string) in p's state.
val get_public_key: #pr:R.preds -> #i:timestamp -> p:principal -> peer:principal -> kt:key_type -> t:string ->
    R.LCrypto (public_key pr i peer kt t) (pki pr)
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 pk t1 -> t0 == t1 /\ (kt = OneTimeDH ==> (exists si. A.is_dh_public_key pr.R.global_usage i pk (readers [V peer si 0]) t))))

// Delete a OneTimeDH key (identified by the usage string) from p's state. Note: in order to be able
// to still refer to the key value in proofs etc., the session in which the key is stored is
// overwritten by a DeletedOneTimeKey session.
val delete_one_time_key: #pr:R.preds -> #i:timestamp -> p:principal -> t:string ->
    R.LCrypto unit (pki pr)
    (requires (fun t0 -> i == trace_len t0))
    (ensures (fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1))



/// Other overwritten functions from LabeledRuntimeAPI
/// --------------------------------------------------

let rand_gen (#pr:R.preds) (l:label) (u:usage) :
    R.LCrypto (i:timestamp & A.secret pr.R.global_usage i l u) (pki pr)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|i,s|) t1 ->
        i == trace_len t0 /\
        trace_len t1 = trace_len t0 + 1 /\
        was_rand_generated_at (trace_len t0) s l u)) =
    let (|i,s|) = R.rand_gen #(pki pr) l u in
    (|i,s|)

type event = CryptoEffect.event

let trigger_event (#pr:R.preds) (p:principal) (ev:event):
    R.LCrypto unit (pki pr)
    (requires (fun t0 -> R.event_pred_at pr (trace_len t0) p ev))
    (ensures (fun t0 (s) t1 ->
         trace_len t1 = trace_len t0 + 1 /\
         did_event_occur_at (trace_len t0) p ev)) =
    R.trigger_event #(pki pr) p ev

let send (#pr:R.preds) (#i:timestamp) (sender:principal) (receiver:principal)
         (message:A.msg pr.R.global_usage i public) : R.LCrypto timestamp (pki pr)
    (requires (fun t0 -> i <= trace_len t0))
    (ensures (fun t0 r t1 ->
          r == trace_len t0 /\
          trace_len t1 = trace_len t0 + 1 /\
          was_message_sent_at (trace_len t0) sender receiver message)) =
    R.send #(pki pr) #i sender receiver message

let receive_i (#pr:R.preds) (index_of_send_event:timestamp) (receiver:principal):
    R.LCrypto (now:timestamp & sender:principal & A.msg pr.R.global_usage now public) (pki pr)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,t|) t1 ->  t0 == t1 /\
          now = trace_len t0 /\
          index_of_send_event < trace_len t0 /\
          (exists sender receiver. was_message_sent_at index_of_send_event sender receiver t))) =
    let (|now,sender,msg|) = R.receive_i #(pki pr) index_of_send_event receiver in
    (|now,sender,msg|)
