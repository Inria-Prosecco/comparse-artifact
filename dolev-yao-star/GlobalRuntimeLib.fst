/// GlobalRuntimeLib (implementation)
/// ==================================
module GlobalRuntimeLib

open SecrecyLabels
open CryptoLib
module W = FStar.Monotonic.Witnessed
friend CryptoLib // in order to get access to mk_rand and sprint_bytes and sprint_generated_rand
open CryptoEffect
friend CryptoEffect //in order to get access to c_get
friend SecrecyLabels // in order to get access to sprint_id

val discard: bool -> Crypto unit (requires (fun t0 -> True))
                   (ensures (fun t0 _ t1 -> t0 == t1))
let discard _ = ()
let tot_print_string s = IO.debug_print_string s

let print_string s = discard (IO.debug_print_string s)

let print_bytes t = print_string (sprint_bytes t)

let sprint_session_state_iv (i:nat) (v:nat) (ss:session_state) : string =
  "Session "^string_of_int i^"(v"^string_of_int v^"): ("^sprint_bytes ss^")"

let rec sprint_session_state_i (del:string) (i:nat) (vs:Seq.seq nat) (ps:state_vec) : Tot string (decreases (Seq.length ps - i))=
  if i < Seq.length ps && Seq.length ps = Seq.length vs
  then if i = Seq.length ps - 1 then sprint_session_state_iv i vs.[i] ps.[i]
       else sprint_session_state_iv i vs.[i] ps.[i]^del^sprint_session_state_i del (i+1) vs ps
  else ""

let sprint_entry (i:nat) (e:entry_t) =
  (if i < 10 then " "^string_of_int i ^ ". " else string_of_int i ^ ". ") ^
  (match e with
  | RandGen t l u -> sprint_generated_rand t
  | Corrupt p s v -> "Compromised "^sprint_id (V p s v)
  | Event p (n,tl) -> "Event "^p^": "^n^"("^String.concat "," (List.Tot.map sprint_bytes tl)^")"
  | Message s r t -> "Message "^s^"->"^r^": "^sprint_bytes t
  | SetState p v ns -> "SetState "^p^": \n    "^sprint_session_state_i "\n    " 0 v ns)

val print_seq_entry: i:nat -> s:Seq.seq entry_t -> Crypto unit
                     (requires fun t0 -> True)
                     (ensures fun t0 _ t1 -> t0 == t1)
                     (decreases (Seq.length s - i))
let rec print_seq_entry (i:nat) (s:Seq.seq entry_t) =
  if i >= Seq.length s then ()
  else (print_string (sprint_entry i s.[i]);
        print_string "\n";
        print_seq_entry (i+1) s)

let print_trace () =
  let t = c_get () in
  print_seq_entry 0 t

let error (#a:Type) (e:string) = cerror #a e
let global_timestamp () = cglobal_timestamp ()
let get () =
  let t = c_get () in
  Ghost.hide t

let corrupt_id (ts:timestamp) (x:id) : Type0 =
    exists p' s' v'. (was_corrupted_before ts p' s' v' /\ covers x (V p' s' v'))

let corrupt_id_lemma ts x = ()
let corrupt_id_covers (ts:timestamp) (x:id) (y:id) = ()

val append_entry: e:entry_t -> Crypto unit
  (requires (fun t0 -> True))
  (ensures (fun t0 s t1 ->
    match s with
    | Error _ -> False
    | Success () ->
      trace_len t1 = trace_len t0 + 1 /\
      trace_entry_at (trace_len t0) e)
  )
let append_entry e =
  let t0 = get() in
  let now = global_timestamp () in
  write_at_end e;
  Seq.un_snoc_snoc t0 e;
  let p = trace_entry_at_pred now e in
  witness p;
  ()

val get_entry: i:nat -> Crypto entry_t
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 s t1 ->
    match s with
    | Error _ -> False
    | Success e ->
      t1 == t0 /\
      trace_entry_at i e)
  )
let get_entry i =
  let t0 = c_get() in
  let e = Seq.index t0 i in
  let pr = trace_entry_at_pred i e in
  witness pr;
  e

let gen l u =
  let now = global_timestamp () in
  let t = mk_rand now l u in
  append_entry (RandGen t l u);
  t

let trigger_event p ev =
  append_entry (Event p ev)

let send p1 p2 t =
  let now = global_timestamp () in
  append_entry (Message p1 p2 t);
  now

let receive_i i p2 =
  let e = get_entry i in
  match e with
  | Message p1 p' m ->
    assert(was_message_sent_at i p1 p' m);
    (p1,m)
  | e -> error "message not found"

let set_state p v s =
  append_entry (SetState p v s)

let get_state_i i p =
  let e = get_entry i in
  match e with
  | SetState p' v s ->
     if p = p' then (v,s)
     else error "state stored by incorrect principal"
  | e -> error "no state stored at given index"

/// get_last_state_before
/// ---------------------

let rec get_last_state_before i p =
  let e = get_entry i in
  match e with
  | SetState p' v s ->
      if p = p' then ( // Check whether this is actually an update for the correct principal
        Some (i,v,s)
      ) else if i > 0 then ( // Is wasn't an update for the correct pricipal
        get_last_state_before (i-1) p
      ) else (
        None //error "update for wrong principal"
      )
  | e ->
      if i > 0 then
        get_last_state_before (i-1) p
      else
        None //error "update not found"

let compromise p s v =
  append_entry (Corrupt p s v)
