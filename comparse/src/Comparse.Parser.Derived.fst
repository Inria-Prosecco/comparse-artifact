module Comparse.Parser.Derived

#set-options "--fuel 0 --ifuel 2"

#push-options "--ifuel 1 --fuel 1"
val for_allP_append: #a:Type -> pre:(a -> prop) -> l1:list a -> l2:list a -> Lemma
  (for_allP pre (l1@l2) <==> for_allP pre l1 /\ for_allP pre l2)
  [SMTPat (for_allP pre (l1@l2))]
let rec for_allP_append #a pre l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> for_allP_append pre t l2
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

let ps_lbytes #bytes #bl n =
  mk_trivial_isomorphism (ps_whole_to_ps_prefix n (refine_whole ps_whole_bytes (ps_whole_length_pred ps_whole_bytes n)))

let ps_lbytes_serialize #bytes #bl n x = ()

let ps_lbytes_is_not_unit #bytes #bl n = ()

let ps_lbytes_is_well_formed #bytes #bl n pre x = assert_norm(for_allP pre [x] <==> pre x)

#push-options "--ifuel 0 --fuel 2"
let ps_lbytes_length #bytes #bl n x =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes)
#pop-options

val isomorphism_subset: #bytes:Type0 -> {|bytes_like bytes|} -> a:Type -> b:Type -> ps_a:parser_serializer_prefix bytes a ->
  a_to_b:(a -> option b) -> b_to_a:(b -> a) ->
  a_to_b_to_a: (xa:a -> squash (match a_to_b xa with | None -> True | Some xb -> xa == b_to_a xb)) ->
  b_to_a_to_b: (xb:b -> squash (a_to_b (b_to_a xb) == Some xb)) ->
  parser_serializer_prefix bytes b
let isomorphism_subset #bytes #bl a b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b =
  let a_pred (xa:a) = Some? (a_to_b xa) in
  let iso = Mkisomorphism_between #(refined a a_pred) #b
    (fun xa -> Some?.v (a_to_b xa))
    (fun xb -> b_to_a_to_b xb; (b_to_a xb))
    (fun xa -> a_to_b_to_a xa)
    (fun xb -> b_to_a_to_b xb)
  in
  isomorphism (refine ps_a a_pred) iso


let ps_nat_lbytes #bytes #bl sz =
  isomorphism_subset (lbytes bytes sz) (nat_lbytes sz) (ps_lbytes sz)
    (fun (x:lbytes bytes sz) -> match to_nat #bytes x with | None -> None | Some y -> Some y)
    (fun (x:nat_lbytes sz) -> from_nat #bytes sz x)
    (fun x -> to_from_nat #bytes x)
    (fun x -> from_to_nat #bytes sz x)

let ps_nat_lbytes_serialize #bytes #bl sz x = ()

let ps_nat_lbytes_is_not_unit #bytes #bl n = ()

let ps_nat_lbytes_is_well_formed #bytes #bl sz pre x = assert_norm(for_allP pre [from_nat sz x] <==> pre (from_nat sz x))

let ps_nat_lbytes_length #bytes #bl sz x = ()

let length_prefix_ps_whole #bytes #bl #a length_pre ps_nat ps_a =
  let b (sz:refined nat length_pre) = refined a (ps_whole_length_pred ps_a sz) in
  mk_isomorphism a
    (bind #bytes #_ #(refined nat length_pre) #b ps_nat (fun sz -> ps_whole_to_ps_prefix sz (refine_whole ps_a (ps_whole_length_pred ps_a sz))))
    (fun (|sz, x|) -> x)
    (fun x -> (|length (ps_a.serialize x), x|))

let length_prefix_ps_whole_serialize #bytes #bl #a length_pre ps_length ps_a x = ()

let length_prefix_ps_whole_is_well_formed #bytes #bl #a length_pre ps_length ps_a pre x =
  let x_serialized = ps_a.serialize x in
  for_allP_append pre (ps_length.serialize (length x_serialized)) [x_serialized];
  assert(is_well_formed_prefix ps_length pre (length x_serialized));
  assert_norm(for_allP pre [x_serialized] <==> pre x_serialized)

let length_prefix_ps_whole_length #bytes #bl #a length_pre ps_length ps_a x =
  let x_serialized = ps_a.serialize x in
  prefixes_length_concat (ps_length.serialize (length x_serialized)) [x_serialized];
  assert_norm (prefixes_length [x_serialized] == length x_serialized)

#push-options "--fuel 1"
val list_unrefb: #a:Type -> #p:(a -> bool) -> list (x:a {p x}) -> l:list a {List.Tot.for_all p l}
let rec list_unrefb #a #p l =
  match l with
  | [] -> []
  | h::t -> h::(list_unrefb t)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val list_unrefb_refb:
  #a:eqtype -> #p:(a -> bool) ->
  l:list a{for_all p l} ->
  Lemma (list_unrefb #a #p (list_refb #a #p l) == l)
let rec list_unrefb_refb #a #p l =
  match l with
  | [] -> ()
  | h::t -> list_unrefb_refb #a #p t
#pop-options

#push-options "--ifuel 1 --fuel 1"
val list_refb_unrefb:
  #a:eqtype -> #p:(a -> bool) ->
  l:list (x:a {p x}) ->
  Lemma (list_refb #a #p (list_unrefb #a #p l) == l)
let rec list_refb_unrefb #a #p l =
  match l with
  | [] -> (
    assert_norm(list_unrefb #a #p (list_refb #a #p []) == [])
  )
  | h::t -> (
    list_refb_unrefb #a #p t;
    assert_norm(list_refb #a #p (list_unrefb #a #p (h::t)) == h::(list_refb #a #p (list_unrefb #a #p t)))
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val map_roundtrip_lemma:
  #a:Type -> #b:Type ->
  f:(a -> b) -> g:(b -> a) ->
  (x:a -> squash (g (f x) == x)) ->
  l:list a ->
  squash (List.Tot.map g (List.Tot.map f l) == l)
let rec map_roundtrip_lemma #a #b f g pf l =
  match l with
  | [] -> ()
  | h::t -> (
    pf h;
    map_roundtrip_lemma f g pf t
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val isomorphism_between_list: #a:Type -> #b:Type -> isomorphism_between a b -> isomorphism_between (list a) (list b)
let isomorphism_between_list #a #b iso =
  let a_to_b (l:list a): list b = List.Tot.map iso.a_to_b l in
  let b_to_a (l:list b): list a = List.Tot.map iso.b_to_a l in
  let a_to_b_to_a (l:list a): squash (b_to_a (a_to_b l) == l) =
    map_roundtrip_lemma iso.a_to_b iso.b_to_a iso.a_to_b_to_a l
  in
  let b_to_a_to_b (l:list b): squash (a_to_b (b_to_a l) == l) =
    map_roundtrip_lemma iso.b_to_a iso.a_to_b iso.b_to_a_to_b l
  in
  {
    a_to_b;
    b_to_a;
    a_to_b_to_a;
    b_to_a_to_b;
  }
#pop-options

let ps_whole_ascii_string #bytes #bl =
  let ascii_string_nonorm = s:string{string_is_ascii s} in
  let list_char_is_ascii (l: list FStar.Char.char) = List.Tot.for_all char_is_ascii l in
  let list_ascii_char = l: list FStar.Char.char{list_char_is_ascii l} in
  let ps_list_ascii_char =
    isomorphism_whole (ps_whole_list #bytes (ps_nat_lbytes 1)) (
      isomorphism_between_list {
        a_to_b = (fun (x:nat_lbytes 1) -> (FStar.Char.char_of_int x <: (c:FStar.Char.char{char_is_ascii c})));
        b_to_a = ascii_char_to_byte;
        a_to_b_to_a = (fun x -> FStar.Char.u32_of_char_of_u32 (FStar.UInt32.uint_to_t x));
        b_to_a_to_b = (fun x -> FStar.Char.char_of_u32_of_char x);
      }
    )
  in
  let ps_list_ascii_char' =
    mk_trivial_isomorphism_whole (
      isomorphism_whole ps_list_ascii_char ({
        a_to_b = (fun (x:list (c:FStar.Char.char{char_is_ascii c})) ->
          list_unrefb #FStar.Char.char #char_is_ascii x
        );
        b_to_a = (fun (x:list_ascii_char) ->
          list_refb #FStar.Char.char #char_is_ascii x
        );
        a_to_b_to_a = (fun x -> list_refb_unrefb #FStar.Char.char #char_is_ascii x);
        b_to_a_to_b = (fun x -> list_unrefb_refb #FStar.Char.char #char_is_ascii x);
      })
    )
  in
  let ps_ascii_string_nonorm =
    isomorphism_whole ps_list_ascii_char' ({
      a_to_b = (fun (x:list_ascii_char) ->
        FStar.String.list_of_string_of_list x;
        (FStar.String.string_of_list x) <: ascii_string_nonorm
      );
      b_to_a = (fun (x:ascii_string_nonorm) ->
        FStar.String.list_of_string x
      );
      a_to_b_to_a = (fun x -> FStar.String.list_of_string_of_list x);
      b_to_a_to_b = (fun x -> FStar.String.string_of_list_of_string x);
    })
  in
  assert_norm(forall x. string_is_ascii x <==> normalize_term (b2t (string_is_ascii x)));
  mk_trivial_isomorphism_whole ps_ascii_string_nonorm

#push-options "--fuel 1 --ifuel 1"
let ps_whole_ascii_string_serialize #bytes #bl x =
  assert ((ps_whole_ascii_string #bytes).serialize x ==
    (ps_whole_list (ps_nat_lbytes 1)).serialize (
      List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val bytes_length_nat_lbytes_1:
  bytes:Type0 -> {|bytes_like bytes|} ->
  l:list (nat_lbytes 1) ->
  Lemma (bytes_length #bytes (ps_nat_lbytes 1) l == List.Tot.length l)
let rec bytes_length_nat_lbytes_1 bytes #bl l =
  match l with
  | [] -> ()
  | h::t -> bytes_length_nat_lbytes_1 bytes t
#pop-options

#push-options "--fuel 1 --ifuel 1"
let ps_whole_ascii_string_length #bytes #bl x =
  ps_whole_ascii_string_serialize #bytes x;
  let the_list = (List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))) in
  ps_whole_list_length #bytes (ps_nat_lbytes 1) the_list;
  bytes_length_nat_lbytes_1 bytes the_list
#pop-options

let ps_whole_ascii_string_is_well_formed #bytes #bl pre x =
  ps_whole_ascii_string_serialize #bytes x;
  let the_list = (List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))) in
  ps_whole_list_is_well_formed #bytes (ps_nat_lbytes 1) pre the_list;
  for_allP_eq (is_well_formed_prefix (ps_nat_lbytes 1) pre) the_list

let ps_null_terminated_ascii_string #bytes #bl =
  let null_terminated_ascii_string_nonorm = s:string{string_is_null_terminated_ascii s} in
  let list_char_is_null_terminated_ascii (l: list FStar.Char.char) = List.Tot.for_all char_is_null_terminated_ascii l in
  let list_null_terminated_ascii_char = l: list FStar.Char.char{list_char_is_null_terminated_ascii l} in
  let ps_list_nonzero_nat_lbytes_1 =
    mk_isomorphism (list (refined (nat_lbytes 1) (pred_not nat_lbytes_1_is_null))) (ps_list_until #bytes (ps_nat_lbytes 1) nat_lbytes_1_is_null)
    (fun (l, last) -> l)
    (fun l -> (l, 0))
  in
  let ps_list_null_terminated_ascii_char =
    isomorphism ps_list_nonzero_nat_lbytes_1 (
      isomorphism_between_list {
        a_to_b = (fun (x:refined (nat_lbytes 1) (pred_not nat_lbytes_1_is_null)) ->
          (FStar.Char.char_of_int x <: (c:FStar.Char.char{char_is_null_terminated_ascii c}))
        );
        b_to_a = null_terminated_ascii_char_to_byte ;
        a_to_b_to_a = (fun x -> FStar.Char.u32_of_char_of_u32 (FStar.UInt32.uint_to_t x));
        b_to_a_to_b = (fun x -> FStar.Char.char_of_u32_of_char x);
      }
    )
  in
  let ps_list_null_terminated_ascii_char': parser_serializer bytes list_null_terminated_ascii_char =
    mk_trivial_isomorphism (
      isomorphism ps_list_null_terminated_ascii_char ({
        a_to_b = (fun (x:list (c:FStar.Char.char{char_is_null_terminated_ascii c})) ->
          list_unrefb #FStar.Char.char #char_is_null_terminated_ascii x
        );
        b_to_a = (fun (x:list_null_terminated_ascii_char) ->
          list_refb #FStar.Char.char #char_is_null_terminated_ascii x
        );
        a_to_b_to_a = (fun x -> list_refb_unrefb #FStar.Char.char #char_is_null_terminated_ascii x);
        b_to_a_to_b = (fun x -> list_unrefb_refb #FStar.Char.char #char_is_null_terminated_ascii x);
      })
    )
  in
  let ps_null_terminated_ascii_string_nonorm =
    isomorphism ps_list_null_terminated_ascii_char' ({
      a_to_b = (fun (x:list_null_terminated_ascii_char) ->
        FStar.String.list_of_string_of_list x;
        (FStar.String.string_of_list x) <: null_terminated_ascii_string_nonorm
      );
      b_to_a = (fun (x:null_terminated_ascii_string_nonorm) ->
        FStar.String.list_of_string x
      );
      a_to_b_to_a = (fun x -> FStar.String.list_of_string_of_list x);
      b_to_a_to_b = (fun x -> FStar.String.string_of_list_of_string x);
    })
  in
  assert_norm(forall x. string_is_null_terminated_ascii x <==> normalize_term (b2t (string_is_null_terminated_ascii x)));
  mk_trivial_isomorphism ps_null_terminated_ascii_string_nonorm

#push-options "--fuel 1 --ifuel 1"
let ps_null_terminated_ascii_string_serialize #bytes #bl x =
  assert((ps_null_terminated_ascii_string #bytes).serialize x ==
    (ps_list_until (ps_nat_lbytes 1) nat_lbytes_1_is_null).serialize
      ((List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string x))),0)
  );
  let a = nat_lbytes 1 in
  let ps_a = ps_nat_lbytes #bytes 1 in
  let pred = nat_lbytes_1_is_null in
  let l = (List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string x))) in
  let last: refined (nat_lbytes 1) (nat_lbytes_1_is_null) = 0 in
  assert(((ps_list_until ps_a pred).serialize (l, last) == (List.Tot.fold_right (@) (List.Tot.map ps_a.serialize l) (ps_a.serialize last)))
  ) by (FStar.Tactics.apply_lemma (`ps_list_until_serialize))
#pop-options

let ps_null_terminated_ascii_string_length #bytes #bl x =
  ps_null_terminated_ascii_string_serialize #bytes x;
  let l = (List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string x))) in
  ps_list_until_length (ps_nat_lbytes #bytes 1) nat_lbytes_1_is_null (l, 0);
  bytes_length_nat_lbytes_1 bytes (List.Tot.map id l)

let ps_null_terminated_ascii_string_is_well_formed #bytes #bl pre x =
  ps_null_terminated_ascii_string_serialize #bytes x;
  let l = (List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string x))) in
  ps_list_until_is_well_formed (ps_nat_lbytes #bytes 1) nat_lbytes_1_is_null pre (l, 0);
  for_allP_eq (is_well_formed_prefix (ps_nat_lbytes 1) pre) l

(*** Parser for variable-length lists ***)

val ps_whole_pre_length_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> pre_length:(nat -> bool) -> parser_serializer_whole bytes (pre_length_bytes bytes pre_length)
let ps_whole_pre_length_bytes #bytes #bl pre_length =
  let length_pred (x:bytes) = pre_length (length (ps_whole_bytes.serialize x)) in
  mk_trivial_isomorphism_whole (refine_whole ps_whole_bytes length_pred)

let ps_pre_length_bytes #bytes #bl pre_length ps_length =
  length_prefix_ps_whole pre_length ps_length (ps_whole_pre_length_bytes pre_length)

let ps_pre_length_bytes_serialize #bytes #bl pre_length ps_length x =
  length_prefix_ps_whole_serialize pre_length ps_length (ps_whole_pre_length_bytes pre_length) x

let ps_pre_length_bytes_is_well_formed #bytes #bl pre_length ps_length pre x =
  length_prefix_ps_whole_is_well_formed pre_length ps_length (ps_whole_pre_length_bytes pre_length) pre x

let ps_pre_length_bytes_length #bytes #bl pre_length ps_length x =
  length_prefix_ps_whole_length pre_length ps_length (ps_whole_pre_length_bytes pre_length) x

val ps_whole_pre_length_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> ps_a:parser_serializer bytes a -> parser_serializer_whole bytes (pre_length_list ps_a pre_length)
let ps_whole_pre_length_list #bytes #bl #a pre_length ps_a =
  let length_pred (x:list a) = pre_length (length ((ps_whole_list ps_a).serialize x)) in
  mk_trivial_isomorphism_whole (refine_whole (ps_whole_list ps_a) length_pred)

let ps_pre_length_list #bytes #bl #a pre_length ps_length ps_a =
  length_prefix_ps_whole pre_length ps_length (ps_whole_pre_length_list pre_length ps_a)

let ps_pre_length_list_serialize #bytes #bl #a pre_length ps_length ps_a x =
  length_prefix_ps_whole_serialize pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) x

let ps_pre_length_list_is_well_formed #bytes #bl #a pre_length ps_length ps_a pre x =
  length_prefix_ps_whole_is_well_formed pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) pre x;
  assert(is_well_formed_whole (ps_whole_pre_length_list pre_length ps_a) pre x <==> is_well_formed_whole (ps_whole_list ps_a) pre x)

let ps_pre_length_list_length #bytes #bl #a pre_length ps_length ps_a x =
  length_prefix_ps_whole_length pre_length ps_length (ps_whole_pre_length_list pre_length ps_a) x

let ps_pre_length_seq #bytes #bl #a pre_length ps_length ps_a =
  FStar.Classical.forall_intro (Seq.lemma_list_seq_bij #a);
  FStar.Classical.forall_intro (Seq.lemma_seq_list_bij #a);
  mk_isomorphism (pre_length_seq ps_a pre_length) (ps_pre_length_list pre_length ps_length ps_a)
    (fun (l:pre_length_list ps_a pre_length) -> Seq.seq_of_list l)
    (fun (s:pre_length_seq ps_a pre_length) -> Seq.seq_to_list s)

let ps_pre_length_seq_is_well_formed #bytes #bl #a pre_length ps_length ps_a pre x = ()

let ps_pre_length_seq_length #bytes #bl #a pre_length ps_length ps_a x = ()

(*** TLS-style length ***)

let ps_tls_nat #bytes #bl r =
  let sz = find_nbytes r.max in
  mk_trivial_isomorphism (refine (ps_nat_lbytes sz) (in_range r))

#push-options "--fuel 1"
let ps_tls_nat_serialize #bytes #bl r x = ()
#pop-options

let ps_tls_nat_length #bytes #bl r x = ()

(*** Unary-style length ***)

val is_bool: nat_lbytes 1 -> bool
let is_bool n = n = 0 || n = 1

type my_bool = refined (nat_lbytes 1) is_bool

val ps_my_bool: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes my_bool
let ps_my_bool #bytes #bl = refine #bytes (ps_nat_lbytes 1) is_bool

val is_zero: my_bool -> bool
let is_zero b = b = 0

val ps_nat_unary: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer bytes nat
let ps_nat_unary #bytes #bl =
  isomorphism (ps_list_until ps_my_bool is_zero) ({
    a_to_b = (fun ((l, _):list_until my_bool is_zero) ->
      List.Tot.length l
    );
    b_to_a = (fun (x:nat) -> (Seq.seq_to_list (Seq.create #(refined my_bool (pred_not is_zero)) x 1)), 0);
    a_to_b_to_a = (fun ((l, _):list_until my_bool is_zero) ->
      List.Tot.index_extensionality l (Seq.seq_to_list (Seq.create (List.Tot.length l) 1))
    );
    b_to_a_to_b = (fun (x:nat) -> ());
  })

val ps_nat_unary_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} ->
  pre:bytes_compatible_pre bytes -> x:nat ->
  Lemma (is_well_formed_prefix ps_nat_unary pre x)
  [SMTPat (is_well_formed_prefix ps_nat_unary pre x)]
let ps_nat_unary_is_well_formed #bytes #bl pre x =
  for_allP_eq (is_well_formed_prefix ps_my_bool pre) (Seq.seq_to_list (Seq.create #(refined my_bool (pred_not is_zero)) x 1))

open FStar.Mul

// Use a "slow" nat parser to derive a more compact one
val ps_nat_accelerate: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes nat -> parser_serializer bytes nat
let ps_nat_accelerate #bytes #bl ps_nat_slow =
  let nbytes_prefix (n:nat): Pure nat (requires True) (ensures fun res -> (n == 0 /\ res == 0) \/ (pow2 (8 * res) <= n /\ n < pow2 (8 * (res+1)))) = (find_nbytes n) - 1 in
  let nbytes_to_pred (nbytes:nat) (n:nat) = (nbytes = 0 && n = 0) || (pow2 (8 * nbytes)) <= n in
  introduce forall (nbytes:nat) (n:nat_lbytes (nbytes+1)). pow2 (8 * nbytes) <= n ==> nbytes == nbytes_prefix n with (
    if pow2 (8 * nbytes) <= n then (
      let found_nbytes = nbytes_prefix n in
      if nbytes < found_nbytes then (
        Math.Lemmas.pow2_le_compat (8 * found_nbytes) (8 * (nbytes+1));
        assert(False)
      ) else if found_nbytes < nbytes then (
        Math.Lemmas.pow2_le_compat (8 * nbytes) (8 * (found_nbytes+1));
        assert(False)
      ) else (
        ()
      )
    ) else (
      ()
    )
  );
  mk_isomorphism nat
    (
      bind #_ #_ #nat #(fun nbytes -> refined (nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)) ps_nat_slow (fun nbytes ->
        refine (ps_nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)
      )
    )
    (fun (|nbytes, n|) -> n)
    (fun n -> (|nbytes_prefix n, n|))

#push-options "--z3rlimit 15"
let ps_true_nat #bytes #bl =
  mk_isomorphism (refined nat true_nat_pred) (ps_nat_accelerate ps_nat_unary) (fun n -> n) (fun n -> n)
#pop-options

(*** QUIC-style length ***)

type nat_lbits (sz:nat) = n:nat{n < pow2 sz}

#push-options "--fuel 0 --ifuel 0 --z3cliopt smt.arith.nl=false"
val euclidean_div_uniqueness: b:pos -> q1:nat -> q2:nat -> r1:nat -> r2:nat -> Lemma
  (requires r1 < b /\ r2 < b /\ (q1*b + r1 == q2*b + r2))
  (ensures q1 == q2 /\ r1 == r2)
let rec euclidean_div_uniqueness b q1 q2 r1 r2 =
  if q2 < q1 then (
    euclidean_div_uniqueness b q2 q1 r2 r1
  ) else (
    if q1 = 0 then (
      FStar.Math.Lemmas.mul_zero_left_is_zero b;
      if 1 <= q2 then (
        FStar.Math.Lemmas.lemma_mult_le_right b 1 q2;
        assert(False)
      ) else ()
    ) else (
      FStar.Math.Lemmas.distributivity_sub_left q1 1 b;
      FStar.Math.Lemmas.distributivity_sub_left q2 1 b;
      euclidean_div_uniqueness b (q1-1) (q2-1) r1 r2
    )
  )
#pop-options

val split_nat_lbits_isomorphism: sz1:nat -> sz2:nat -> isomorphism_between (nat_lbits (sz1+sz2)) (nat_lbits sz1 & nat_lbits sz2)
let split_nat_lbits_isomorphism sz1 sz2 =
  let open FStar.Math.Lemmas in
  introduce forall (n:nat_lbits (sz1+sz2)). n / (pow2 sz2) < pow2 sz1 with (
    lemma_div_lt_nat n (sz1+sz2) sz2
  );
  introduce forall (n1:nat_lbits sz1) (n2:nat_lbits sz2). n1 * (pow2 sz2) + n2 < pow2 (sz1+sz2) with (
    lemma_mult_le_right (pow2 sz2) n1 ((pow2 sz1)-1);
    distributivity_sub_left (pow2 sz1) 1 (pow2 sz2);
    pow2_plus sz1 sz2
  );
  introduce forall (n:nat_lbits (sz1+sz2)). (n / (pow2 sz2)) * (pow2 sz2) + (n % (pow2 sz2)) == n with (
    euclidean_division_definition n (pow2 sz2)
  );
  introduce forall (n1:nat_lbits sz1) (n2:nat_lbits sz2). (n1 * (pow2 sz2) + n2) / (pow2 sz2) == n1 /\ (n1 * (pow2 sz2) + n2) % (pow2 sz2) == n2 with (
    let n = (n1 * (pow2 sz2) + n2) in
    euclidean_division_definition n (pow2 sz2);
    euclidean_div_uniqueness (pow2 sz2) n1 ((n1 * (pow2 sz2) + n2) / (pow2 sz2)) n2 ((n1 * (pow2 sz2) + n2) % (pow2 sz2))
  );
  mk_isomorphism_between #(nat_lbits (sz1+sz2)) #(nat_lbits sz1 & nat_lbits sz2)
    (fun n -> (n / (pow2 sz2), n % (pow2 sz2)))
    (fun (n1, n2) -> n1 * (pow2 sz2) + n2)

val flip_isomorphism: #a:Type -> #b:Type -> isomorphism_between a b -> isomorphism_between b a
let flip_isomorphism #a #b iso =
  {
    a_to_b = iso.b_to_a;
    b_to_a = iso.a_to_b;
    a_to_b_to_a = iso.b_to_a_to_b;
    b_to_a_to_b = iso.a_to_b_to_a;
  }

val concat_nat_lbits_isomorphism: sz1:nat -> sz2:nat -> isomorphism_between (nat_lbits sz1 & nat_lbits sz2) (nat_lbits (sz1+sz2))
let concat_nat_lbits_isomorphism sz1 sz2 =
  flip_isomorphism (split_nat_lbits_isomorphism sz1 sz2)

val split_nat_lbits: #bytes:Type0 -> {|bytes_like bytes|} -> sz1:nat -> sz2:nat -> parser_serializer bytes (nat_lbits (sz1+sz2)) -> parser_serializer bytes (nat_lbits sz1 & nat_lbits sz2)
let split_nat_lbits #bytes #bl sz1 sz2 ps_n =
  isomorphism ps_n (split_nat_lbits_isomorphism sz1 sz2)

#push-options "--z3rlimit 25"
let ps_quic_nat #bytes #bl =
  let open FStar.Math.Lemmas in
  assert_norm(normalize_term (pow2 62) == pow2 62);
  assert_norm(pow2 2 = 4);
  let loglen_to_rem_nbits (loglen:nat_lbits 2) = (8*((pow2 loglen)-1)) in
  let first_byte_to_len (first_byte:((nat_lbits 2) & (nat_lbits 6))): Pure nat (requires True) (fun res -> res <= 7) =
    let (loglen, b1) = first_byte in
    pow2_le_compat 3 loglen;
    assert_norm(pow2 3 = 8);
    (pow2 loglen)-1
  in
  let first_byte_to_type (first_byte:((nat_lbits 2) & (nat_lbits 6))) =
    nat_lbytes (first_byte_to_len first_byte)
  in
  let first_byte_to_parser (first_byte:((nat_lbits 2) & (nat_lbits 6))): parser_serializer_prefix bytes (first_byte_to_type first_byte) =
    let len = first_byte_to_len first_byte in
    ps_nat_lbytes len
  in
  let ps_first_byte = split_nat_lbits #bytes 2 6 (mk_trivial_isomorphism (ps_nat_lbytes 1)) in
  let loglen_property (loglen:nat_lbits 2) (n:quic_nat) =
    n < pow2 (6 + loglen_to_rem_nbits loglen) /\ (loglen <> 0 ==> pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= n)
  in
  let n_to_loglen (n:quic_nat): Pure (nat_lbits 2) (requires True) (ensures fun loglen -> loglen_property loglen n) =
    assert_norm (loglen_to_rem_nbits 0 = 0);
    assert_norm (loglen_to_rem_nbits 1 = 8*1);
    assert_norm (loglen_to_rem_nbits 2 = 8*3);
    assert_norm (loglen_to_rem_nbits 3 = 8*7);
    if n < pow2 (6 + loglen_to_rem_nbits 0) then 0
    else if n < pow2 (6 + loglen_to_rem_nbits 1) then 1
    else if n < pow2 (6 + loglen_to_rem_nbits 2) then 2
    else 3
  in
  let n_to_loglen_unique (loglen:nat_lbits 2) (n:quic_nat): Lemma (requires loglen_property loglen n) (ensures loglen == n_to_loglen n) =
    if loglen < n_to_loglen n then (
      pow2_lt_compat loglen ((n_to_loglen n)-1);
      pow2_lt_compat (6 + loglen_to_rem_nbits ((n_to_loglen n)-1)) (6 + loglen_to_rem_nbits loglen)
    ) else if loglen > n_to_loglen n then (
      pow2_lt_compat (loglen-1) (n_to_loglen n);
      pow2_lt_compat (6 + loglen_to_rem_nbits (loglen-1)) (6 + loglen_to_rem_nbits (n_to_loglen n))
    ) else ()
  in

  let a_to_b (x:(dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type)): option quic_nat =
    let (|first_byte, bn|) = x in
    let (loglen, b1) = first_byte in
    let len = first_byte_to_len first_byte in
    pow2_le_compat 62 (6+8*len);
    let res = (concat_nat_lbits_isomorphism 6 (8*len)).a_to_b (b1, bn) in
    if loglen = 0 || pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= res then (
      Some res
    ) else (
      None
    )
  in
  let b_to_a (n:quic_nat): (dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type) =
    let loglen = n_to_loglen n in
    let (b1, bn) = (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).b_to_a n in
    (|(loglen, b1), bn|)
  in
  let a_to_b_to_a (xa:(dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type)): squash (match a_to_b xa with | None -> True | Some xb -> xa == b_to_a xb) =
    let (|first_byte, bn|) = xa in
    let (loglen, b1) = first_byte in
    let len = first_byte_to_len first_byte in
    (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).a_to_b_to_a (b1, bn);
    pow2_le_compat 62 (6+8*len);
    let res = (concat_nat_lbits_isomorphism 6 (8*len)).a_to_b (b1, bn) in
    if loglen = 0 then ()
    else if pow2 (6 + loglen_to_rem_nbits (loglen-1)) <= res then
      n_to_loglen_unique loglen res
    else ()
  in
  let b_to_a_to_b (n:quic_nat): squash (a_to_b (b_to_a n) == Some n) =
    let loglen = n_to_loglen n in
    (concat_nat_lbits_isomorphism 6 (loglen_to_rem_nbits loglen)).b_to_a_to_b n
  in
  isomorphism_subset #bytes #bl (dtuple2 ((nat_lbits 2) & (nat_lbits 6)) first_byte_to_type) quic_nat (bind ps_first_byte first_byte_to_parser)
    a_to_b b_to_a
    a_to_b_to_a
    b_to_a_to_b

let ps_quic_nat_length #bytes #bl n =
  assert_norm(pow2 0 == 1);
  assert_norm(pow2 1 == 2);
  assert_norm(pow2 2 == 4);
  assert_norm(pow2 3 == 8)
