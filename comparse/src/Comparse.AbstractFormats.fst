module Comparse.AbstractFormats

open Comparse

type cbytes = Seq.seq UInt8.t

instance cbytes_bytes_like: bytes_like cbytes = seq_u8_bytes_like

(*** Basic types ***)

type message_format (bytes:Type0) {|bytes_like bytes|} (a:Type) =
  a -> bytes -> prop

type parser (bytes:Type0) {|bytes_like bytes|} (a:Type) =
  bytes -> option a

type serializer (bytes:Type0) {|bytes_like bytes|} (a:Type) =
  a -> bytes

(*** Relation between formats and parser/serializers ***)

val is_parser_for:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser bytes a -> message_format bytes a ->
  prop
let is_parser_for #bytes #bl #a parse mf =
  (forall b.
    match parse b with
    | None -> True
    | Some m -> m `mf` b
  ) /\ (
    forall b. (exists m. m `mf` b) ==> Some? (parse b)
  )

val is_serializer_for:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  serializer bytes a -> message_format bytes a ->
  prop
let is_serializer_for #bytes #bl #a serialize mf =
  forall m. m `mf` (serialize m)

val is_induced_by:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  (parser bytes a & serializer bytes a) ->
  prop
let is_induced_by #bytes #bl #a mf (parse, serialize) =
  forall m b. m `mf` b <==> ((Some m == parse b) \/ (serialize m == b))

(*** Refined types ***)

type parser_for (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (mf:message_format bytes a) =
  parse:parser bytes a{parse `is_parser_for` mf}

type serializer_for (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (mf:message_format bytes a) =
  serialize:serializer bytes a{serialize `is_serializer_for` mf}

type message_format_for
  (#bytes:Type0) {|bytes_like bytes|} (#a:Type)
  (parse:parser bytes a) (serialize:serializer bytes a) =
  mf:message_format bytes a{mf `is_induced_by` (parse, serialize)}

(*** Security properties ***)

val non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  prop
let non_ambiguous #bytes #bl #a mf =
  forall m1 m2 b. m1 `mf` b /\ m2 `mf` b ==> m1 == m2

val unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  prop
let unique_representant #bytes #bl #a mf =
  forall m b1 b2. m `mf` b1 /\ m `mf` b2 ==> b1 == b2

(*** Helper functions for security properties ***)

val intro_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a ->
  (m1:a -> m2:a -> b:bytes -> Lemma (requires m1 `mf` b /\ m2 `mf` b) (ensures m1 == m2)) ->
  Lemma (non_ambiguous mf)
let intro_non_ambiguous #bytes #bl #a mf proof =
  introduce forall m1 m2 b. m1 `mf` b /\ m2 `mf` b ==> m1 == m2 with (
    introduce _ ==> _ with _. (
      proof m1 m2 b
    )
  )

val intro_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a ->
  (m:a -> b1:bytes -> b2:bytes -> Lemma (requires m `mf` b1 /\ m `mf` b2) (ensures b1 == b2)) ->
  Lemma (unique_representant mf)
let intro_unique_representant #bytes #bl #a mf proof =
  introduce forall m b1 b2. m `mf` b1 /\ m `mf` b2 ==> b1 == b2 with (
    introduce _ ==> _ with _. (
      proof m b1 b2
    )
  )

(*** Equivalent security properties on parser / serializers ***)

val ps_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser bytes a -> serializer bytes a ->
  prop
let ps_non_ambiguous #bytes #bl #a parse serialize =
  forall m. parse (serialize m) == Some m

val ps_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser bytes a -> serializer bytes a ->
  prop
let ps_unique_representant #bytes #bl #a parse serialize =
  forall b.
    match parse b with
    | None -> True
    | Some m -> serialize m == b

val non_ambiguous_eq_1:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a -> parse:parser_for mf -> serialize:serializer_for mf ->
  Lemma
  (requires non_ambiguous mf)
  (ensures ps_non_ambiguous parse serialize)
let non_ambiguous_eq_1 #bytes #bl #a mf parse serialize = ()

val non_ambiguous_eq_2:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parse:parser bytes a -> serialize:serializer bytes a ->
  mf:message_format_for parse serialize ->
  Lemma
  (requires ps_non_ambiguous parse serialize)
  (ensures non_ambiguous mf)
let non_ambiguous_eq_2 #bytes #bl #a parse serialize mf = ()

val unique_representant_eq_1:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a -> parse:parser_for mf -> serialize:serializer_for mf ->
  Lemma
  (requires unique_representant mf)
  (ensures ps_unique_representant parse serialize)
let unique_representant_eq_1 #bytes #bl #a mf parse serialize = ()

val unique_representant_eq_2:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parse:parser bytes a -> serialize:serializer bytes a ->
  mf:message_format_for parse serialize ->
  Lemma
  (requires ps_unique_representant parse serialize)
  (ensures unique_representant mf)
let unique_representant_eq_2 #bytes #bl #a parse serialize mf = ()

(*** Additional properties ***)

val non_empty:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  prop
let non_empty #bytes #bl #a mf =
  forall m b. m `mf` b ==> 1 <= length b

// This is the definition from the paper
val non_extensible_paper:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  prop
let non_extensible_paper #bytes #bl #a mf =
  forall m1 m2 b1 b2. m1 `mf` b1 /\ m2 `mf` (b1 `concat` b2) ==> b2 == empty

// This (proven equivalent later) definition is more gentle with symbolic bytes
// This is because the bytes equality inside it has an homogenous number of concatenations
val non_extensible:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  prop
let non_extensible #bytes #bl #a mf =
  forall m1 m2 pref1 suf1 pref2 suf2.
    pref1 `concat` suf1 == pref2 `concat` suf2 /\
    m1 `mf` pref1 /\
    m2 `mf` pref2
    ==>
    pref1 == pref2

(*** Helper function ***)

val intro_non_extensible:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a ->
  (m1:a -> m2:a -> pref1:bytes -> suf1:bytes -> pref2:bytes -> suf2:bytes -> Lemma (requires pref1 `concat` suf1 == pref2 `concat` suf2 /\ m1 `mf` pref1 /\ m2 `mf` pref2) (ensures pref1 == pref2)) ->
  Lemma (non_extensible mf)
let intro_non_extensible #bytes #bl #a mf proof =
  introduce forall m1 m2 pref1 suf1 pref2 suf2. pref1 `concat` suf1 == pref2 `concat` suf2 /\ m1 `mf` pref1 /\ m2 `mf` pref2 ==> pref1 == pref2 with (
    introduce _ ==> _ with _. (
      proof m1 m2 pref1 suf1 pref2 suf2
    )
  )

(*** Equivalence between two non-extensibility conditions ***)

// On concrete bytes
val non_extensible_eq1:
  #a:Type ->
  mf:message_format cbytes a ->
  Lemma
  (requires non_extensible mf)
  (ensures non_extensible_paper mf)
let non_extensible_eq1 #a mf =
  introduce forall m1 m2 b1 b2. m1 `mf` b1 /\ m2 `mf` (b1 `concat` b2) ==> b2 == empty with (
    introduce _ ==> _ with _. (
      assert((b1 `concat` b2) `Seq.eq` ((b1 `concat` b2) `concat` empty));
      assert(b1 == (b1 `concat` b2));
      assert(length (b1 `concat` b2) == length b1 + length b2);
      assert(b2 `Seq.eq` empty)
    )
  )

// On concrete bytes
val non_extensible_eq2:
  #a:Type ->
  mf:message_format cbytes a ->
  Lemma
  (requires non_extensible_paper mf)
  (ensures non_extensible mf)
let non_extensible_eq2 #a mf =
  intro_non_extensible mf (fun m1 m2 pref1 suf1 pref2 suf2 ->
    if length pref1 = length pref2 then (
      split_concat pref1 suf1;
      split_concat pref2 suf2
    ) else (
      if length pref1 < length pref2 then (
        assert((Seq.slice (pref1 `concat` suf1) 0 (length pref2)) `Seq.eq` (pref1 `concat` (Seq.slice suf1 0 (length pref2 - length pref1))));
        assert((Seq.slice (pref2 `concat` suf2) 0 (length pref2)) `Seq.eq` pref2)
      ) else (
        assert((Seq.slice (pref2 `concat` suf2) 0 (length pref1)) `Seq.eq` (pref2 `concat` (Seq.slice suf2 0 (length pref1 - length pref2))));
        assert((Seq.slice (pref1 `concat` suf1) 0 (length pref1)) `Seq.eq` pref1)
      )
    )
  )

(*** Non-emptiness lemma ***)

val non_empty_eq_1:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  mf:message_format bytes a -> parse:parser_for mf -> serialize:serializer_for mf ->
  Lemma
  (requires non_empty mf)
  (ensures forall x. 1 <= length (serialize x) /\ (forall b. length b = 0 ==> parse b == None))
let non_empty_eq_1 #bytes #bl #a mf parse serialize = ()

val non_empty_eq_2:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parse:parser bytes a -> serialize:serializer bytes a ->
  mf:message_format_for parse serialize ->
  Lemma
  (requires (forall x. 1 <= length (serialize x)) /\ (forall b. length b = 0 ==> parse b == None))
  (ensures non_empty mf)
let non_empty_eq_2 #bytes #bl #a parse serialize mf = ()

(*** Dependent pair combinator ***)

val mf_dtuple2:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> #b:(a -> Type) ->
  message_format bytes a -> (x:a -> message_format bytes (b x)) ->
  message_format bytes (dtuple2 a b)
let mf_dtuple2 #bytes #bl #a #b mf_a mf_b = fun m buf ->
  let (|m_a, m_b|) = m in
  exists b1 b2. buf == b1 `concat` b2 /\
  m_a `mf_a` b1 /\
  m_b `mf_b m_a` b2

val mf_dtuple2_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:(a -> Type) ->
  mf_a:message_format bytes a -> mf_b:(x:a -> message_format bytes (b x)) ->
  Lemma
  (requires non_extensible mf_a /\ non_ambiguous mf_a /\ (forall x. non_ambiguous (mf_b x)))
  (ensures non_ambiguous (mf_dtuple2 mf_a mf_b))
let mf_dtuple2_non_ambiguous #a #b mf_a mf_b =
  intro_non_ambiguous (mf_dtuple2 mf_a mf_b) (fun m1 m2 b ->
    let (|m1_a, m1_b|) = m1 in
    let (|m2_a, m2_b|) = m2 in
    eliminate exists b1a b1b b2a b2b.
      b == b1a `concat` b1b /\
      m1_a `mf_a` b1a /\
      m1_b `mf_b m1_a` b1b /\
      b == b2a `concat` b2b /\
      m2_a `mf_a` b2a /\
      m2_b `mf_b m2_a` b2b
    returns m1 == m2
    with _. (
      split_concat b1a b1b;
      split_concat b2a b2b
    )
  )

val mf_dtuple2_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:(a -> Type) ->
  mf_a:message_format bytes a -> mf_b:(x:a -> message_format bytes (b x)) ->
  Lemma
  (requires unique_representant mf_a /\ (forall x. unique_representant (mf_b x)))
  (ensures unique_representant (mf_dtuple2 mf_a mf_b))
let mf_dtuple2_unique_representant #bytes #bl #a #b mf_a mf_b = ()

// Proof on concrete bytes
val mf_dtuple2_non_extensible:
  #a:Type -> #b:(a -> Type) ->
  mf_a:message_format cbytes a -> mf_b:(x:a -> message_format cbytes (b x)) ->
  Lemma
  (requires non_extensible mf_a /\ non_ambiguous mf_a /\ (forall x. non_extensible (mf_b x)))
  (ensures non_extensible (mf_dtuple2 mf_a mf_b))
let mf_dtuple2_non_extensible #a #b mf_a mf_b =
  intro_non_extensible (mf_dtuple2 mf_a mf_b) (fun m1 m2 pref1 suf1 pref2 suf2 ->
    let (|m1_a, m1_b|) = m1 in
    let (|m2_a, m2_b|) = m2 in
    eliminate exists b1a b1b b2a b2b.
      pref1 == b1a `concat` b1b /\
      m1_a `mf_a` b1a /\
      m1_b `mf_b m1_a` b1b /\
      pref2 == b2a `concat` b2b /\
      m2_a `mf_a` b2a /\
      m2_b `mf_b m2_a` b2b
    returns pref1 == pref2
    with _. (
      assert((b1a `concat` (b1b `concat` suf1)) `Seq.eq` ((b1a `concat` b1b) `concat` suf1));
      assert((b2a `concat` (b2b `concat` suf2)) `Seq.eq` ((b2a `concat` b2b) `concat` suf2));
      split_concat b1a (b1b `concat` suf1);
      split_concat b2a (b2b `concat` suf2)
    )
  )

val mf_dtuple2_non_empty:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:(a -> Type) ->
  mf_a:message_format bytes a -> mf_b:(x:a -> message_format bytes (b x)) ->
  Lemma
  (requires non_empty mf_a \/ (forall x. non_empty (mf_b x)))
  (ensures non_empty (mf_dtuple2 mf_a mf_b))
let mf_dtuple2_non_empty #bytes #bl #a #b mf_a mf_b = ()

(*** List combinator ***)

val for_all2P: #a:Type -> #b:Type -> (a -> b -> prop) -> la:list a -> lb:list b{List.Tot.length la == List.Tot.length lb} -> prop
let rec for_all2P #a #b p la lb =
  match la, lb with
  | [], [] -> True
  | ha::ta, hb::tb ->
    p ha hb /\ for_all2P p ta tb

val mf_list:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  message_format bytes a ->
  message_format bytes (list a)
let mf_list #bytes #bl #a mf_a = fun m b ->
  exists (bs:list bytes).
    List.Tot.length m == List.Tot.length bs /\
    b == List.Tot.fold_right concat bs empty /\
    for_all2P mf_a m bs

val mf_list_non_ambiguous_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf_a:message_format bytes a ->
  l1:list a -> l2:list a -> b:bytes ->
  Lemma
  (requires
    non_extensible mf_a /\ non_empty mf_a /\ non_ambiguous mf_a /\
    l1 `mf_list mf_a` b /\ l2 `mf_list mf_a` b
  )
  (ensures l1 == l2)
  (decreases List.Tot.length l1)
let rec mf_list_non_ambiguous_aux #bytes #bl #a mf_a l1 l2 b =
  if List.Tot.length l1 > List.Tot.length l2 then mf_list_non_ambiguous_aux mf_a l2 l1 b
  else (
    match l1, l2 with
    | [], [] -> ()
    | [], h2::t2 -> (
      eliminate exists (bs:list bytes).
        List.Tot.length l2 == List.Tot.length bs /\
        b == List.Tot.fold_right concat bs empty /\
        for_all2P mf_a l2 bs
      returns False
      with _. (
        assert(length b == 0)
      )
    )
    | h1::t1, h2::t2 -> (
      eliminate exists (bs1:list bytes) (bs2:list bytes).
        List.Tot.length l1 == List.Tot.length bs1 /\
        b == List.Tot.fold_right concat bs1 empty /\
        for_all2P mf_a l1 bs1 /\
        List.Tot.length l2 == List.Tot.length bs2 /\
        b == List.Tot.fold_right concat bs2 empty /\
        for_all2P mf_a l2 bs2
      returns l1 == l2
      with _. (
        match bs1, bs2 with
        | hbs1::tbs1, hbs2::tbs2 -> (
          split_concat hbs1 (List.Tot.fold_right concat tbs1 empty);
          split_concat hbs2 (List.Tot.fold_right concat tbs2 empty);
          mf_list_non_ambiguous_aux mf_a t1 t2 (List.Tot.fold_right concat tbs1 empty <: bytes)
        )
      )
    )
  )

val mf_list_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf_a:message_format bytes a ->
  Lemma
  (requires
    non_extensible mf_a /\ non_empty mf_a /\ non_ambiguous mf_a
  )
  (ensures non_ambiguous (mf_list mf_a))
let mf_list_non_ambiguous #bytes #bl #a mf_a =
  intro_non_ambiguous (mf_list mf_a) (fun m1 m2 b ->
    mf_list_non_ambiguous_aux mf_a m1 m2 b
  )

val mf_list_unique_representant_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf_a:message_format bytes a ->
  l:list a -> b1:bytes -> b2:bytes ->
  Lemma
  (requires
     unique_representant mf_a /\
    l `mf_list mf_a` b1 /\ l `mf_list mf_a` b2
  )
  (ensures b1 == b2)
  (decreases l)
let rec mf_list_unique_representant_aux #bytes #bl #a mf_a l b1 b2 =
  match l with
  | [] -> ()
  | h::t -> (
    eliminate exists (bs1:list bytes) (bs2:list bytes).
      List.Tot.length l == List.Tot.length bs1 /\
      b1 == List.Tot.fold_right concat bs1 empty /\
      for_all2P mf_a l bs1 /\
      List.Tot.length l == List.Tot.length bs2 /\
      b2 == List.Tot.fold_right concat bs2 empty /\
      for_all2P mf_a l bs2
    returns b1 == b2
    with _. (
      match bs1, bs2 with
      | hbs1::tbs1, hbs2::tbs2 -> (
        split_concat hbs1 (List.Tot.fold_right concat tbs1 empty);
        split_concat hbs2 (List.Tot.fold_right concat tbs2 empty);
        mf_list_unique_representant_aux mf_a t (List.Tot.fold_right concat tbs1 empty <: bytes) (List.Tot.fold_right concat tbs2 empty <: bytes)
      )
    )
  )

val mf_list_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf_a:message_format bytes a ->
  Lemma
  (requires unique_representant mf_a)
  (ensures unique_representant (mf_list mf_a))
let mf_list_unique_representant #bytes #bl #a mf_a =
  intro_unique_representant (mf_list mf_a) (fun m b1 b2 ->
    mf_list_unique_representant_aux mf_a m b1 b2
  )

(*** Isomorphism combinator ***)

val mf_iso:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  message_format bytes a -> isomorphism_between a b ->
  message_format bytes b
let mf_iso #bytes #bl #a #b mf_a iso = fun m buf ->
  iso.b_to_a m `mf_a` buf

val mf_iso_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> iso:isomorphism_between a b ->
  Lemma
  (requires non_ambiguous mf_a)
  (ensures non_ambiguous (mf_iso mf_a iso))
let mf_iso_non_ambiguous #bytes #bl #a #b mf_a iso =
  introduce forall x. iso.a_to_b (iso.b_to_a x) == x with iso.b_to_a_to_b x

val mf_iso_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> iso:isomorphism_between a b ->
  Lemma
  (requires unique_representant mf_a)
  (ensures unique_representant (mf_iso mf_a iso))
let mf_iso_unique_representant #bytes #bl #a #b mf_a iso =
  introduce forall x. iso.a_to_b (iso.b_to_a x) == x with iso.b_to_a_to_b x

val mf_iso_non_extensible:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> iso:isomorphism_between a b ->
  Lemma
  (requires non_extensible mf_a)
  (ensures non_extensible (mf_iso mf_a iso))
let mf_iso_non_extensible #bytes #bl #a #b mf_a iso =
  introduce forall x. iso.a_to_b (iso.b_to_a x) == x with iso.b_to_a_to_b x

val mf_iso_non_empty:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> iso:isomorphism_between a b ->
  Lemma
  (requires non_empty mf_a)
  (ensures non_empty (mf_iso mf_a iso))
let mf_iso_non_empty #bytes #bl #a #b mf_a iso =
  introduce forall x. iso.a_to_b (iso.b_to_a x) == x with iso.b_to_a_to_b x

(*** Refinement combinator ***)

type refinedP (a:Type) (pred:a -> prop) = x:a{pred x}

val mf_refinedP:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  message_format bytes a -> pred:(a -> prop) ->
  message_format bytes (refinedP a pred)
let mf_refinedP #bytes #bl #a mf_a pred = fun m buf ->
  m `mf_a` buf

val mf_refinedP_non_ambiguous:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> pred:(a -> prop) ->
  Lemma
  (requires non_ambiguous mf_a)
  (ensures non_ambiguous (mf_refinedP mf_a pred))
let mf_refinedP_non_ambiguous #bytes #bl #a mf_a pred = ()

val mf_refinedP_unique_representant:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> pred:(a -> prop) ->
  Lemma
  (requires unique_representant mf_a)
  (ensures unique_representant (mf_refinedP mf_a pred))
let mf_refinedP_unique_representant #bytes #bl #a mf_a pred = ()

val mf_refinedP_non_extensible:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> pred:(a -> prop) ->
  Lemma
  (requires non_extensible mf_a)
  (ensures non_extensible (mf_refinedP mf_a pred))
let mf_refinedP_non_extensible #bytes #bl #a mf_a pred = ()

val mf_refinedP_non_empty:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> #b:Type ->
  mf_a:message_format bytes a -> pred:(a -> prop) ->
  Lemma
  (requires non_empty mf_a)
  (ensures non_empty (mf_refinedP mf_a pred))
let mf_refinedP_non_empty #bytes #bl #a mf_a pred = ()

(*** Length restriction ***)

val restrict_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf:message_format bytes a -> l:nat ->
  a -> prop
let restrict_length #bytes #bl #a mf l m =
  forall b. m `mf` b ==> length b == l

val restrict_length_non_extensible:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type ->
  mf:message_format bytes a -> l:nat ->
  Lemma (non_extensible (mf_refinedP mf (restrict_length mf l)))
let restrict_length_non_extensible #bytes #bl #a mf l =
  intro_non_extensible (mf_refinedP mf (restrict_length mf l)) (fun m1 m2 pred1 suf1 pred2 suf2 ->
    split_concat pred1 suf1;
    split_concat pred2 suf2
  )
