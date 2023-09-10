/// LabeledRuntimeAPI
/// ==================
///
/// This module provides APIs to interact with the global state, i.e., trace, allowing to set/get
/// local state, generate nonces, send and receive messages etc.  It also provides an API to trigger
/// protocol-specific events, which are typically used to make formulation and proofs of security
/// properties more convenient.
///
/// A primer on global state, trace, and trace invariants
/// -----------------------------------------------------
///
/// The stateful APIs here all enforce certain invariants on the global trace. In addition to some
/// generic invariants, e.g., enforcing labeling and usage rules, these invariants are
/// protocol-specific and are used to prove the desired security properties.  On a technical level,
/// these protocol-specific trace invariants are the ``trace_preds`` declared below.  Each of the
/// stateful APIs requires a concrete ``trace_preds`` as input and requires the global state to
/// satisfy these preds (such a global state is called a *valid trace*) when calling the API, and
/// similarly each API guarantees to leave the global state as a valid trace.
module LabeledRuntimeAPI

open SecrecyLabels
open CryptoLib
open CryptoEffect
open GlobalRuntimeLib
open LabeledCryptoAPI

/// .. _labeledruntimeapi_preds_definition:
///
/// Trace invariants
/// ----------------
///
/// Container type for protocol-specific trace invariants.

noeq type trace_preds (g:global_usage) = {
  can_trigger_event: timestamp -> principal -> event -> prop;
  session_st_inv: trace_idx:timestamp -> principal -> session:nat -> version:nat -> bytes -> prop;
  session_st_inv_lemma: i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
                  Lemma (session_st_inv i p si vi st ==>
                         is_msg g i st (readers [V p si vi]));
  session_st_inv_later: i:timestamp -> j:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
                   Lemma ((session_st_inv i p si vi st /\ later_than j i) ==>
                           session_st_inv j p si vi st)
}

/// Container type for protocol-specific trace invariants and secret usage rules. Protocol
/// implementations have to define the contents of this container and pass it to all stateful APIs
/// (as described above).
noeq type preds = {
  global_usage: global_usage;
  trace_preds: trace_preds global_usage
}

/// TODO DOC
let event_pred_at (pr:preds) n p e = pr.trace_preds.can_trigger_event n p e

let event_pred (pr:preds) n p e =
    (exists i. later_than n i /\ event_pred_at pr i p e)

let state_inv (pr:preds) (idx:timestamp) (prin:principal) (version_vec:version_vec) (st:state_vec) : prop =
  (Seq.length version_vec = Seq.length st) /\
  (forall i. i < Seq.length version_vec ==> pr.trace_preds.session_st_inv idx prin i version_vec.[i] st.[i])

let session_st_inv_later (pr:preds) (i:timestamp) (j:timestamp) (p:principal) (si:nat) (vi:nat) (st:bytes) :
    Lemma ((pr.trace_preds.session_st_inv i p si vi st /\ later_than j i) ==> pr.trace_preds.session_st_inv j p si vi st)
          [SMTPat (pr.trace_preds.session_st_inv i p si vi st); SMTPat (later_than j i)] =
          pr.trace_preds.session_st_inv_later i j p si vi st

let state_inv_later (pr:preds) (i:timestamp) (j:timestamp) (p:principal) (vv:version_vec) (st:state_vec) :
    Lemma ((state_inv pr i p vv st /\ later_than j i) ==> state_inv pr j p vv st)
          [SMTPat (state_inv pr i p vv st); SMTPat (later_than j i)] = ()


/// Definition of a valid trace
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// This predicate is the combination of all our trace invariants. All parties, including the
/// attacker, must preserve this predicate (see :doc:`AttackerAPI` for attacker typeability, i.e., a
/// proof that this predicate does not restrict the attacker in a way which would violate our
/// attacker model).
///
/// The exact details of this predicate are hidden from API clients, we instead expose the relevant
/// facts as lemmas.

val valid_trace: preds -> trace -> Type0

val valid_trace_event_lemma: pr:preds -> t:trace -> i:timestamp -> s:principal -> e:event ->
  Lemma ((valid_trace pr t /\ i < trace_len t /\ did_event_occur_at i s e) ==>
          event_pred_at pr i s e)
        [SMTPat (valid_trace pr t); SMTPat (did_event_occur_at i s e)]

val valid_trace_respects_state_inv: (pr:preds) -> (trace:trace) -> (i:timestamp) -> (p:principal) -> (v:version_vec)-> (s:state_vec) ->
  Lemma (requires (valid_trace pr trace /\  i < trace_len trace /\  state_was_set_at i p v s))
        (ensures (state_inv pr i p v s))
        [SMTPat (valid_trace pr trace); SMTPat (state_was_set_at i p v s)]


/// Stateful application API
/// ------------------------
///
/// The LCrypto effect
/// ~~~~~~~~~~~~~~~~~~
///
/// An effect abbreviation for CRYPTO functions that preserve trace validity, which is basically a shorter
/// way of writing :code:`... Crypto a (requires fun t0 -> valid_trace pr t0) (ensures fun _ _ t1 -> valid_trace pr t1)`
///
/// All stateful APIs and their client functions (i.e., protocol implementations) will usually use this effect.

effect LCRYPTO (a:Type) (pr:preds) (pre:pre_t) (post:(t0:trace{pre t0} -> result a -> trace -> Type0)) =
  CRYPTO a (fun p s0 ->
    valid_trace pr s0 /\ pre s0 /\
    (forall (x:result a) (s1:trace). (valid_trace pr s1 /\
                                 later_than (trace_len s1) (trace_len s0) /\
                                 post s0 x s1) ==> p x s1))

effect LCrypto (a:Type) (pr:preds) (pre:pre_t) (post:(t0:trace{pre t0} -> a -> trace -> Type0)) =
  LCRYPTO a pr pre (fun s0 r s1 ->
    (Error? r ==> True) /\
    (Success? r ==> post s0 (Success?.v r) s1))

/// Nonce Generation
/// ~~~~~~~~~~~~~~~~
///
/// Generate a fresh nonce with the exact label and usage. Returns the timestamp at which the nonce
/// creation was recorded in the trace, as well as the actual nonce.
val rand_gen: #pr:preds -> l:label -> u:usage ->
  LCrypto (i:timestamp & secret pr.global_usage i l u) pr
    (requires (fun t0 -> True))
    (ensures (fun t0 (|i,s|) t1 ->
        i == trace_len t0 /\
        trace_len t1 = trace_len t0 + 1 /\
        was_rand_generated_at (trace_len t0) s l u))

/// Protocol Events
/// ~~~~~~~~~~~~~~~
val trigger_event: #pr:preds -> p:principal -> ev:event -> LCrypto unit pr
    (requires (fun t0 -> event_pred_at pr (trace_len t0) p ev))
    (ensures (fun t0 (s) t1 ->
         trace_len t1 = trace_len t0 + 1 /\
         did_event_occur_at (trace_len t0) p ev))


/// Send and receive messages
/// ~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// Returns the timestamp at which the message sending was recorded in the trace. Note how we
/// require the sent message to be labeled such that the label :ref:`can flow to public
/// <labeledcryptoapi_labeling_description>`.  This enforces our labeling rules: The attacker can of
/// course learn any message sent over the network; we capture this by requiring the label on any
/// sent message to flow to public, i.e., the sender has to prove that the attacker will not learn
/// anything from this message which was previously labeled as a secret.
val send: #pr:preds -> #i:timestamp -> sender:principal -> receiver:principal ->
          message:msg pr.global_usage i public -> LCrypto timestamp pr
    (requires (fun t0 -> i <= trace_len t0))
    (ensures (fun t0 r t1 ->
          r == trace_len t0 /\
          trace_len t1 = trace_len t0 + 1 /\
          was_message_sent_at (trace_len t0) sender receiver message))

/// Returns the current trace length, the sender of the message as recorded in the trace, and the
/// actual message. Note that the sender value here is NOT authenticated, i.e., the actual creator
/// of the received message may be any party, including the attacker.
val receive_i: #pr:preds -> index_of_send_event:timestamp -> receiver:principal ->
          LCrypto (now:timestamp & sender:principal & msg pr.global_usage now public) pr
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,sender,t|) t1 ->  t0 == t1 /\
          now = trace_len t0 /\
          index_of_send_event < trace_len t0 /\
          (exists sender receiver. was_message_sent_at index_of_send_event sender receiver t)))


/// Modify and retrieve local state
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// These first two functions always operate on the full local state and are enough to model any
/// operations on local states (i.e., the additional session API below is not strictly needed).

val set_state: #pr:preds -> p:principal -> v:version_vec -> s:state_vec -> LCrypto unit pr
    (requires (fun t0 -> Seq.length v == Seq.length s /\
                      state_inv pr (trace_len t0) p v s))
    (ensures (fun t0 r t1 -> trace_len t1 = trace_len t0 + 1 /\
                          state_was_set_at (trace_len t0) p v s))

val get_last_state: #pr:preds -> p:principal ->
    LCrypto (timestamp & version_vec & state_vec) pr
     (requires (fun t0 -> True))
     (ensures (fun t0 (now,v,s) t1 ->  t0 == t1 /\
              (exists i. i < now /\ state_was_set_at i p v s) /\
              now = trace_len t0 /\
              state_inv pr now p v s))

/// Session-based API for local state
/// .................................
///
/// A common pattern in many protocol implementations using the above local state APIs is to get the
/// current local state, extract a particular session from it (see :ref:`SecrecyLabels
/// <secrecylabels_id_def>` for details on what a "session" is in this context), modify that
/// session, construct a new local state, with the only change being that one session, and set the
/// whole local state again.  This a) requires quite a bit of boilerplate code to extract and
/// re-insert the one session of interest, and b) results in a heavier proof burden: Validity of the
/// whole local state (instead of just the one changed session) must be proven.
///
/// Hence, the following session-based API can be used to get/set individual sessions within the
/// local state.
// TODO This API does not support proof of liveness (i.e., proving that a protocol run can finish)
val new_session_number:
  #pr:preds ->  p:principal ->  LCrypto nat pr
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0)

val new_session:
  #pr:preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat -> st:bytes ->
  LCrypto unit pr
  (requires fun t0 -> trace_len t0 == i /\ pr.trace_preds.session_st_inv i p si vi st)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val update_session:
  #pr:preds -> #i:timestamp -> p:principal -> si:nat -> vi:nat ->
  st:bytes ->
  LCrypto unit pr
  (requires fun t0 -> trace_len t0 == i /\ pr.trace_preds.session_st_inv i p si vi st)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val get_session:
  #pr:preds -> #i:timestamp -> p:principal -> si:nat ->
  LCrypto (vi:nat & msg pr.global_usage i (readers [V p si vi])) pr
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 (|vi,st|) t1 -> t1 == t0 /\
                               pr.trace_preds.session_st_inv i p si vi st)

val find_session:
  #pr:preds -> #i:timestamp -> p:principal -> f:(si:nat -> vi:nat -> st:bytes -> bool) ->
  LCrypto (option (si:nat & vi:nat & msg pr.global_usage i (readers [V p si vi]))) pr
  (requires fun t0 -> trace_len t0 == i)
  (ensures fun t0 r t1 -> t1 == t0 /\
                       (match r with
                        | None -> True // TODO maybe expose non-existence of such a session?
                        | Some (|si,vi,st|) -> f si vi st /\ // TODO maybe expose relation to get_session
                                              pr.trace_preds.session_st_inv i p si vi st))
