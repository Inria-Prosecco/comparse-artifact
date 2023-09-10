module Comparse.Parser.Builtins

#set-options "--fuel 0 --ifuel 2"

#push-options "--fuel 1"
let rec for_allP_eq #a pre l =
  match l with
  | [] -> ()
  | h::t -> for_allP_eq pre t
#pop-options

let is_not_unit #bytes #bl #a ps_a = forall (x:a). 1 <= prefixes_length (ps_a.serialize x)

let is_well_formed_prefix_weaken #bytes #bl #a ps_a pre_strong pre_weak x =
  for_allP_eq pre_strong (ps_a.serialize x);
  for_allP_eq pre_weak (ps_a.serialize x)

(*** Helper functions ***)

#push-options "--ifuel 1 --fuel 1"
val for_allP_append: #a:Type -> pre:(a -> prop) -> l1:list a -> l2:list a -> Lemma
  (for_allP pre (l1@l2) <==> for_allP pre l1 /\ for_allP pre l2)
  [SMTPat (for_allP pre (l1@l2))]
let rec for_allP_append #a pre l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> for_allP_append pre t l2
#pop-options

#push-options "--ifuel 1 --fuel 1"
val add_prefixes_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> suffix:bytes -> Lemma
  (add_prefixes l1 (add_prefixes l2 suffix) == add_prefixes (l1@l2) suffix)
let rec add_prefixes_add_prefixes l1 l2 suffix =
  match l1 with
  | [] -> ()
  | h::t -> add_prefixes_add_prefixes t l2 suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (length (add_prefixes l suffix) == prefixes_length l + length suffix)
let rec add_prefixes_length #bytes #bl l suffix =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes);
  match l with
  | [] -> ()
  | h::t ->
    add_prefixes_length t suffix;
    concat_length h (add_prefixes t suffix)
#pop-options

val prefixes_is_empty: #bytes:Type0 -> {|bytes_like bytes|} -> list bytes -> bool
let prefixes_is_empty l = List.Tot.for_all (fun b -> length b = 0) l

#push-options "--fuel 1 --ifuel 1"
val for_allP_pre_to_pre_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> l:list bytes -> suffix:bytes -> Lemma
  (requires for_allP pre l /\ pre suffix)
  (ensures pre (add_prefixes l suffix))
let rec for_allP_pre_to_pre_add_prefixes #bytes #bl pre l suffix =
  match l with
  | [] -> ()
  | h::t -> for_allP_pre_to_pre_add_prefixes pre t suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val pre_add_prefixes_to_for_allP_pre: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> l:list bytes -> suffix:bytes -> Lemma
  (requires pre (add_prefixes l suffix))
  (ensures for_allP pre l /\ pre suffix)
let rec pre_add_prefixes_to_for_allP_pre #bytes #bl pre l suffix =
  match l with
  | [] -> ()
  | h::t -> (
    split_concat h (add_prefixes t suffix);
    assert(split (add_prefixes l suffix) (length h) == Some (h, add_prefixes t suffix));
    pre_add_prefixes_to_for_allP_pre pre t suffix
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val prefixes_length_concat: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> Lemma
  (prefixes_length (l1@l2) == (prefixes_length l1) + (prefixes_length l2))
let rec prefixes_length_concat #bytes #bl l1 l2 =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes);
  match l1 with
  | [] -> ()
  | h::t -> prefixes_length_concat t l2
#pop-options

(*** Parser for basic types ***)

let ps_unit #bytes #bl =
  {
    parse = (fun b -> Some ((), b));
    serialize = (fun _ -> []);
    parse_serialize_inv = (fun _ b -> assert_norm(add_prefixes [] b == b));
    serialize_parse_inv = (fun buf -> assert_norm(add_prefixes [] buf == buf));
  }

let ps_unit_serialize #bytes #bl x = ()

let ps_unit_is_well_formed #bytes #bl pre x = assert_norm(for_allP pre [] <==> True)

#push-options "--ifuel 0 --fuel 1"
let ps_unit_length #bytes #bl x =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes)
#pop-options

let ps_whole_bytes #bytes #bl =
  {
    parse = (fun x -> Some x);
    serialize = (fun x -> x);
    parse_serialize_inv = (fun _ -> ());
    serialize_parse_inv = (fun _ -> ());
  }

let ps_whole_bytes_serialize #bytes #bl b = ()

(*** Dependent pair combinator ***)
(*** (non-extensible flavor) ***)

let bind #bytes #bl #a #b ps_a ps_b =
  let parse_ab (buf:bytes): option (dtuple2 a b & bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, buf_suffix) -> begin
      match (ps_b xa).parse buf_suffix with
      | None -> None
      | Some (xb, buf_suffix_suffix) -> (
        Some ((|xa, xb|), buf_suffix_suffix)
      )
    end
  in
  let serialize_ab (x:dtuple2 a b): list bytes =
    let (|xa, xb|) = x in
    let la = ps_a.serialize xa in
    let lb = (ps_b xa).serialize xb in
    la@lb
  in

  ({
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (|xa, xb|) (suffix:bytes) ->
      let la = ps_a.serialize xa in
      let lb = ((ps_b xa).serialize xb) in
      ps_a.parse_serialize_inv xa (add_prefixes lb suffix);
      (ps_b xa).parse_serialize_inv xb suffix;
      add_prefixes_add_prefixes la lb suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some ((|xa, xb|), suffix) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix;
        add_prefixes_add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb) suffix
    );
  })

let bind_serialize #bytes #bl #a #b ps_a ps_b xa xb = ()

let bind_is_not_unit #bytes #bl #a #b ps_a ps_b =
  introduce forall x. 1 <= prefixes_length ((bind ps_a ps_b).serialize x) with (
    let (|xa, xb|) = x in
    prefixes_length_concat (ps_a.serialize xa) ((ps_b xa).serialize xb)
  )

let bind_is_well_formed #bytes #bl #a #b ps_a ps_b pre xa xb = ()

let bind_length #bytes #bl #a #b ps_a ps_b xa xb =
  prefixes_length_concat (ps_a.serialize xa) ((ps_b xa).serialize xb)

(*** Dependent pair combinator ***)
(*** (extensible flavor) ***)

let bind_whole #bytes #bl #a #b ps_a ps_b =
  let parse (buf:bytes): option (dtuple2 a b) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, suffix) -> (
      match (ps_b xa).parse suffix with
      | None -> None
      | Some xb -> Some (|xa, xb|)
    )
  in
  let serialize (x:dtuple2 a b): bytes =
    let (|xa, xb|) = x in
    add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb)
  in
  {
    parse = parse;
    serialize = serialize;
    parse_serialize_inv = (fun (|xa, xb|) ->
      let la = ps_a.serialize xa in
      let lb = (ps_b xa).serialize xb in
      ps_a.parse_serialize_inv xa lb;
      (ps_b xa).parse_serialize_inv xb
    );
    serialize_parse_inv = (fun buf ->
      match parse buf with
      | None -> ()
      | Some (|xa, xb|) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let xb = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix
    );
  }

let bind_whole_serialize #bytes #bl #a #b ps_a ps_b xa xb = ()

let bind_whole_is_well_formed_whole #bytes #bl #a #b ps_a ps_b pre xa xb =
  introduce is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|) ==> is_well_formed_prefix ps_a pre xa /\ is_well_formed_whole (ps_b xa) pre xb
  with _. (
    pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize xa) ((ps_b xa).serialize xb)
  );
  introduce is_well_formed_prefix ps_a pre xa /\ is_well_formed_whole (ps_b xa) pre xb ==> is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|)
  with _. (
    for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize xa) ((ps_b xa).serialize xb)
  )

(*** Isomorphism combinator ***)
(*** (non-extensible flavor) ***)

let isomorphism #bytes #bl #a #b ps_a iso =
  let parse_b buf =
    match ps_a.parse buf with
    | Some (xa, l) -> Some (iso.a_to_b xa, l)
    | None -> None
  in
  let serialize_b xb =
    ps_a.serialize (iso.b_to_a xb)
  in
  {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv (iso.b_to_a x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some (xa, l) -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
  }

let isomorphism_serialize #bytes #bl #a #b ps_a iso x = ()

let isomorphism_is_not_unit #bytes #bl #a #b ps_a iso = ()

let isomorphism_is_well_formed #bytes #bl #a #b ps_a iso pre xb = ()

let isomorphism_length #bytes #bl #a #b ps_a iso xb = ()

(*** Isomorphism combinator ***)
(*** (extensible flavor) ***)

let isomorphism_whole #bytes #bl #a #b ps_a iso =
  let parse_b (buf:bytes): option b =
    match ps_a.parse buf with
    | Some xa -> Some (iso.a_to_b xa)
    | None -> None
  in
  let serialize_b (xb:b): bytes =
    ps_a.serialize (iso.b_to_a xb)
  in
  {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv (iso.b_to_a x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some xa -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
  }

let isomorphism_whole_serialize #bytes #bl #a #b ps_a iso x = ()

let isomorphism_whole_is_well_formed #bytes #bl #a #b ps_a iso pre xb = ()

(*** Refinement combinator ***)
(*** (non-extensible flavor) ***)

let refine #bytes #bl #a ps_a pred =
  {
    parse = (fun buf ->
      match ps_a.parse buf with
      | Some (x, suffix) ->
        if pred x then Some ((x <: refined a pred), suffix)
        else None
      | None -> None
    );
    serialize = (fun x -> ps_a.serialize x);
    parse_serialize_inv = (fun x suffix -> ps_a.parse_serialize_inv x suffix);
    serialize_parse_inv = (fun buf -> ps_a.serialize_parse_inv buf);
  }

let refine_serialize #bytes #bl #a ps_a pred x = ()

let refine_is_not_unit #bytes #bl #a ps_a pred = ()

let refine_is_well_formed #bytes #bl #a ps_a pred pre x = ()

let refine_length #bytes #bl #a ps_a pred x = ()

(*** Refinement combinator ***)
(*** (extensible flavor) ***)

let refine_whole #bytes #bl #a ps_a pred =
  {
    parse = (fun buf ->
      match ps_a.parse buf with
      | Some x ->
        if pred x then Some (x <: refined a pred)
        else None
      | None -> None
    );
    serialize = (fun x -> ps_a.serialize x);
    parse_serialize_inv = (fun x -> ps_a.parse_serialize_inv x);
    serialize_parse_inv = (fun buf -> ps_a.serialize_parse_inv buf);
  }

let refine_whole_serialize #bytes #bl #a ps_a pred x = ()

(*** List combinator ***)

//The following functions are defined here because F* can't reason on recursive functions defined inside a function
#push-options "--fuel 1"
val _parse_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> buf:bytes -> Tot (option (list a)) (decreases (length (buf <: bytes)))
let rec _parse_la #bytes #bl #a ps_a buf =
  if recognize_empty buf then (
    Some []
  ) else if length (buf <: bytes) = 0 then (
    None
  ) else (
    match ps_a.parse (buf <: bytes) with
    | None -> None
    | Some (h, suffix) -> begin
      if length suffix >= length (buf <: bytes) then (
        None
      ) else (
        match _parse_la ps_a suffix with
        | None -> None
        | Some t -> Some (h::t)
      )
    end
  )
#pop-options

#push-options "--fuel 1"
val _serialize_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> l:list a -> bytes
let rec _serialize_la #bytes #bl #a ps_a l =
  match l with
  | [] -> empty
  | h::t ->
    add_prefixes (ps_a.serialize h) (_serialize_la ps_a t)
#pop-options

#push-options "--fuel 1"
let ps_whole_list #bytes #bl #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a): bytes = _serialize_la ps_a l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> empty_length #bytes ()
    | h::t ->
      ps_a.parse_serialize_inv h (serialize_la t);
      let suffix = (_serialize_la ps_a t) in
      if prefixes_length (ps_a.serialize h) = 0 then (
        empty_length #bytes ();
        ps_a.parse_serialize_inv h empty;
        add_prefixes_length (ps_a.serialize h) empty;
        assert(False)
      ) else (
        empty_length #bytes ();
        add_prefixes_length (ps_a.serialize h) suffix;
        parse_serialize_inv_la t
      )
  in

  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (length (buf <: bytes))) =
    if recognize_empty buf then (
      ()
    ) else if length (buf <: bytes) = 0 then (
      ()
    ) else (
       match parse_la buf with
       | None -> ()
       | Some l ->
         let (_, suffix) = Some?.v (ps_a.parse buf) in
         ps_a.serialize_parse_inv buf;
         serialize_parse_inv_la suffix
    )
  in
  {
    parse = parse_la;
    serialize = serialize_la;
    parse_serialize_inv = parse_serialize_inv_la;
    serialize_parse_inv = serialize_parse_inv_la;
  }
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_serialize #bytes #bl #a ps_a l =
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> ()
  | h::t -> ps_whole_list_serialize ps_a t
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_is_well_formed #bytes #bl #a ps_a pre l =
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> ()
  | h::t -> (
    introduce is_well_formed_whole (ps_whole_list ps_a) pre l ==> for_allP (is_well_formed_prefix ps_a pre) l
    with _. (
      ps_whole_list_is_well_formed ps_a pre t;
      pre_add_prefixes_to_for_allP_pre pre (ps_a.serialize h) (_serialize_la ps_a t)
    );
    introduce for_allP (is_well_formed_prefix ps_a pre) l ==> is_well_formed_whole (ps_whole_list ps_a) pre l
    with _. (
      ps_whole_list_is_well_formed ps_a pre t;
      for_allP_pre_to_pre_add_prefixes pre (ps_a.serialize h) (_serialize_la ps_a t)
    )
  )
#pop-options

#push-options "--fuel 1"
let rec ps_whole_list_length #bytes #bl #a ps_a l =
  assert_norm (forall l. (ps_whole_list ps_a).serialize l == _serialize_la ps_a l);
  match l with
  | [] -> empty_length #bytes ()
  | h::t ->
    add_prefixes_length (ps_a.serialize h) (_serialize_la ps_a t);
    ps_whole_list_length ps_a t
#pop-options

(*** Another list combinator ***)

val _parse_list_until:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser_serializer bytes a -> pred:(a -> bool) ->
  b:bytes ->
  Tot (option (list_until a pred & bytes)) (decreases length b)
let rec _parse_list_until #bytes #bl #a ps_a pred b =
  match ps_a.parse b with
  | None -> None
  | Some (h, suffix) -> (
    if pred h then
      Some (([], h), suffix)
    else (
      add_prefixes_length (ps_a.serialize h) suffix;
      ps_a.serialize_parse_inv b;
      match _parse_list_until ps_a pred suffix with
      | None -> None
      | Some ((t, last), suffix) ->
        Some ((h::t, last), suffix)
    )
  )

val _serialize_list_until:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser_serializer bytes a -> pred:(a -> bool) ->
  list_until a pred ->
  list bytes
let _serialize_list_until #bytes #bl #a ps_a pred (l, last) =
  List.Tot.fold_right (@) (List.Tot.map ps_a.serialize l) (ps_a.serialize last)

#push-options "--fuel 1 --ifuel 1"
let ps_list_until #bytes #bl #a ps_a pred =
  let rec parse_serialize_inv' (l:list (refined a (pred_not pred))) (last:refined a pred) (suffix:bytes): Lemma (_parse_list_until ps_a pred (add_prefixes (_serialize_list_until ps_a pred (l, last)) suffix) == Some ((l, last), suffix)) =
    match l with
    | [] -> ps_a.parse_serialize_inv last suffix
    | h::t -> (
      add_prefixes_add_prefixes (ps_a.serialize h) (_serialize_list_until ps_a pred (t, last)) suffix;
      ps_a.parse_serialize_inv h (add_prefixes (_serialize_list_until ps_a pred (t, last)) suffix);
      parse_serialize_inv' t last suffix
    )
  in
  let rec parse_serialize_inv (l:list_until a pred) (suffix:bytes): Lemma (_parse_list_until ps_a pred (add_prefixes (_serialize_list_until ps_a pred l) suffix) == Some (l, suffix)) =
    let (l, last) = l in
    parse_serialize_inv' l last suffix
  in
  let rec serialize_parse_inv (buf:bytes): Lemma (ensures (match _parse_list_until ps_a pred buf with | Some (l, suffix) -> buf == add_prefixes (_serialize_list_until ps_a pred l) suffix | None -> True)) (decreases length buf) =
    match _parse_list_until ps_a pred buf with
    | None -> ()
    | Some ((l, last), suffix) -> (
      let Some (h, suffix1) = ps_a.parse buf in
      ps_a.serialize_parse_inv buf;
      if pred h then ()
      else (
        let Some ((t, last'), suffix2) = _parse_list_until ps_a pred suffix1 in
        add_prefixes_length (ps_a.serialize h) suffix1;
        serialize_parse_inv suffix1;
        add_prefixes_add_prefixes (ps_a.serialize h) (_serialize_list_until ps_a pred (t, last')) suffix
      )
    )
  in

  let not_unit (l:list_until a pred): Lemma(1 <= prefixes_length (_serialize_list_until ps_a pred l)) =
    let (l, last) = l in
    match l with
    | [] -> ()
    | h::t -> prefixes_length_concat (ps_a.serialize h) (_serialize_list_until ps_a pred (t, last))
  in
  FStar.Classical.forall_intro not_unit;
  {
    parse = _parse_list_until ps_a pred;
    serialize = _serialize_list_until ps_a pred;
    parse_serialize_inv = parse_serialize_inv;
    serialize_parse_inv = serialize_parse_inv;
  }
#pop-options

let ps_list_until_serialize #bytes #bl #a ps_a pred x =
  normalize_term_spec ((ps_list_until ps_a pred).serialize x)

#push-options "--fuel 1 --ifuel 1"
val ps_list_until_is_well_formed_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a -> pred:(a -> bool) ->
  pre:bytes_compatible_pre bytes -> l:list (refined a (pred_not pred)) -> last:refined a pred ->
  Lemma
  (ensures is_well_formed_prefix (ps_list_until ps_a pred) pre (l, last) <==> (
    for_allP (is_well_formed_prefix ps_a pre) l /\
    is_well_formed_prefix ps_a pre last
  ))
  (decreases l)
let rec ps_list_until_is_well_formed_aux #bytes #bl #a ps_a pred pre l last =
  assert_norm(forall l. (ps_list_until ps_a pred).serialize (l, last) == List.Tot.fold_right (@) (List.Tot.map ps_a.serialize l) (ps_a.serialize last));
  match l with
  | [] -> ()
  | h::t ->
    ps_list_until_is_well_formed_aux ps_a pred pre t last;
    for_allP_append pre (ps_a.serialize h) ((ps_list_until ps_a pred).serialize (t, last))
#pop-options

let ps_list_until_is_well_formed #bytes #bl #a ps_a pred pre (l, last) =
  ps_list_until_is_well_formed_aux ps_a pred pre l last

#push-options "--fuel 1 --ifuel 1"
val ps_list_until_length_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a -> pred:(a -> bool) ->
  l:list (refined a (pred_not pred)) -> last:refined a pred ->
  Lemma
  (prefixes_length ((ps_list_until ps_a pred).serialize (l, last)) == (
    bytes_length ps_a (List.Tot.map id l) +
    prefixes_length (ps_a.serialize last)
  ))
let rec ps_list_until_length_aux #bytes #bl #a ps_a pred l last =
  assert_norm(forall l. (ps_list_until ps_a pred).serialize (l, last) == List.Tot.fold_right (@) (List.Tot.map ps_a.serialize l) (ps_a.serialize last));
  match l with
  | [] -> ()
  | h::t -> (
    ps_list_until_length_aux ps_a pred t last;
    prefixes_length_concat (ps_a.serialize h) (_serialize_list_until ps_a pred (t, last))
  )
#pop-options

let ps_list_until_length #bytes #bl #a ps_a pred x =
  let (l, last) = x in
  ps_list_until_length_aux ps_a pred l last

(*** Conversion between prefix and whole parsers ***)

let ps_prefix_to_ps_whole #bytes #bl #a ps_a =
  let parse_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if recognize_empty suffix then
        Some x
      else
        None
  in
  let serialize_a (x:a): bytes =
    add_prefixes (ps_a.serialize x) empty
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x ->
      ps_a.parse_serialize_inv x empty;
      empty_length #bytes ()
    );
    serialize_parse_inv = (fun buf ->
      match parse_a buf with
      | None -> ()
      | Some _ -> (
        let (x, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.serialize_parse_inv buf
      )
    );
  }

let ps_prefix_to_ps_whole_serialize #bytes #bl #a ps_a x = ()

let ps_prefix_to_ps_whole_is_well_formed #bytes #bl #a ps_a pre x =
  introduce is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x ==> is_well_formed_prefix ps_a pre x
  with _. (
    pre_add_prefixes_to_for_allP_pre #bytes #bl pre (ps_a.serialize x) empty
  );
  introduce is_well_formed_prefix ps_a pre x ==> is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x
  with _. (
    for_allP_pre_to_pre_add_prefixes #bytes #bl pre (ps_a.serialize x) empty
  )

let ps_prefix_to_ps_whole_length #bytes #bl #a ps_a x =
  empty_length #bytes ();
  add_prefixes_length (ps_a.serialize x) empty

let ps_whole_to_ps_prefix #bytes #bl #a len ps_a =
  let parse_a (buf:bytes) =
    match split buf len with
    | None -> None
    | Some (x_lbytes, suffix) -> (
      match ps_a.parse x_lbytes with
      | None -> None
      | Some x_a -> Some (x_a, suffix)
    )
  in
  let serialize_a (x_a:a): list bytes =
    let x_serialized = ps_a.serialize x_a in
    [x_serialized]
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x_a suffix ->
      let x_serialized = ps_a.serialize x_a in
      let sz = (length x_serialized) in
      ps_a.parse_serialize_inv x_a;
      concat_length x_serialized suffix;
      split_concat x_serialized suffix;
      assert_norm(add_prefixes [x_serialized] suffix == concat x_serialized suffix)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x_a, suffix) ->
        let (x_lbytes, _) = Some?.v (split buf len) in
        concat_split buf len;
        ps_a.serialize_parse_inv x_lbytes;
        assert_norm(add_prefixes [ps_a.serialize x_a] suffix == concat (ps_a.serialize x_a) suffix)
    );
  }

let ps_whole_to_ps_prefix_serialize #bytes #bl #a len ps_a x = ()

#push-options "--fuel 1 --ifuel 0"
let ps_whole_to_ps_prefix_is_not_unit #bytes #bl #a len ps_a =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes)
#pop-options
