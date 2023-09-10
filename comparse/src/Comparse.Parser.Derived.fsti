module Comparse.Parser.Derived

open FStar.List.Tot
open Comparse.Parser.Builtins
open Comparse.Bytes.Typeclass
open Comparse.Tactic.Attributes
open Comparse.Utils

(*** Parser for basic types ***)

type lbytes (bytes:Type0) {|bytes_like bytes|} (n:nat) = b:bytes{length b == n}
val ps_lbytes:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  n:nat ->
  parser_serializer_prefix bytes (lbytes bytes n)

val ps_lbytes_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  n:nat ->
  x:lbytes bytes n ->
  Lemma ((ps_lbytes n).serialize x == [x])
  [SMTPat ((ps_lbytes n).serialize x)]

val ps_lbytes_is_not_unit:
  #bytes:Type0 -> {| bl:bytes_like bytes |} -> n:nat ->
  Lemma
    (requires 1 <= n)
    (ensures is_not_unit (ps_lbytes #bytes #bl n))
    [SMTPat (is_not_unit (ps_lbytes #bytes #bl n))]

val ps_lbytes_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> n:nat ->
  pre:bytes_compatible_pre bytes -> x:lbytes bytes n ->
  Lemma (is_well_formed_prefix (ps_lbytes n) pre x <==> pre (x <: bytes))
  [SMTPat (is_well_formed_prefix (ps_lbytes n) pre x)]

val ps_lbytes_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> n:nat ->
  x:lbytes bytes n ->
  Lemma (prefixes_length ((ps_lbytes n).serialize x) == n)
  [SMTPat (prefixes_length ((ps_lbytes n).serialize x))]

[@@is_parser; is_parser_for (`%nat_lbytes)]
val ps_nat_lbytes:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sz:nat ->
  parser_serializer_prefix bytes (nat_lbytes sz)

val ps_nat_lbytes_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sz:nat ->
  x:nat_lbytes sz ->
  Lemma ((ps_nat_lbytes #bytes sz).serialize x == [from_nat sz x])
  [SMTPat ((ps_nat_lbytes #bytes sz).serialize x)]

val ps_nat_lbytes_is_not_unit:
  #bytes:Type0 -> {| bl:bytes_like bytes |} -> n:nat ->
  Lemma
    (requires 1 <= n)
    (ensures is_not_unit (ps_nat_lbytes #bytes #bl n))
    [SMTPat (is_not_unit (ps_nat_lbytes #bytes #bl n))]

val ps_nat_lbytes_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> sz:nat ->
  pre:bytes_compatible_pre bytes -> x:nat_lbytes sz ->
  Lemma (is_well_formed_prefix (ps_nat_lbytes sz) pre x)
  [SMTPat (is_well_formed_prefix (ps_nat_lbytes sz) pre x)]

val ps_nat_lbytes_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> sz:nat ->
  x:nat_lbytes sz ->
  Lemma (prefixes_length #bytes ((ps_nat_lbytes sz).serialize x) == sz)
  [SMTPat (prefixes_length #bytes ((ps_nat_lbytes sz).serialize x))]

(*** Conversion between prefix and whole parsers ***)

type nat_parser_serializer (bytes:Type0) {| bytes_like bytes |} (pre_length:nat -> bool)= ps:parser_serializer bytes (refined nat pre_length){forall pre n. is_well_formed_prefix ps pre n}

val length_prefix_ps_whole:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> nat_parser_serializer bytes length_pre ->
  ps_a:parser_serializer_whole bytes a{forall x. length_pre (length (ps_a.serialize x))} ->
  parser_serializer bytes a

val length_prefix_ps_whole_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> ps_length:nat_parser_serializer bytes length_pre ->
  ps_a:parser_serializer_whole bytes a{forall x. length_pre (length (ps_a.serialize x))} ->
  x:a ->
  Lemma ((length_prefix_ps_whole length_pre ps_length ps_a).serialize x == (ps_length.serialize (length (ps_a.serialize x))) @ [ps_a.serialize x])
  [SMTPat ((length_prefix_ps_whole length_pre ps_length ps_a).serialize x)]

val length_prefix_ps_whole_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> ps_length:nat_parser_serializer bytes length_pre ->
  ps_a:parser_serializer_whole bytes a{forall x. length_pre (length (ps_a.serialize x))} ->
  pre:bytes_compatible_pre bytes -> x:a -> Lemma
  (is_well_formed_prefix (length_prefix_ps_whole length_pre ps_length ps_a) pre x <==> is_well_formed_whole ps_a pre x)

val length_prefix_ps_whole_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  length_pre:(nat -> bool) -> ps_length:nat_parser_serializer bytes length_pre ->
  ps_a:parser_serializer_whole bytes a{forall x. length_pre (length (ps_a.serialize x))} ->
  x:a -> Lemma
  (prefixes_length ((length_prefix_ps_whole length_pre ps_length ps_a).serialize x) == (prefixes_length (ps_length.serialize (length (ps_a.serialize x)))) + (length (ps_a.serialize x)))


(*** Whole parsers ***)

let char_is_ascii (x:FStar.Char.char) = FStar.Char.int_of_char x < 256
let string_is_ascii (s:string) = List.Tot.for_all char_is_ascii (FStar.String.list_of_string s)
type ascii_string = s:string{normalize_term (b2t (string_is_ascii s))}
let ascii_char_to_byte (c:FStar.Char.char{char_is_ascii c}): nat_lbytes 1 = FStar.Char.int_of_char c


val ps_whole_ascii_string:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_whole bytes ascii_string

val ps_whole_ascii_string_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:ascii_string ->
  Lemma ((ps_whole_ascii_string #bytes).serialize x ==
    (ps_whole_list (ps_nat_lbytes 1)).serialize (
      List.Tot.map ascii_char_to_byte (List.Tot.list_refb #_ #char_is_ascii (FStar.String.list_of_string x))
    )
  )
  [SMTPat ((ps_whole_ascii_string #bytes).serialize x)]

val ps_whole_ascii_string_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:ascii_string ->
  Lemma (length ((ps_whole_ascii_string #bytes).serialize x) == FStar.String.strlen x)
  [SMTPat (length ((ps_whole_ascii_string #bytes).serialize x))]

val ps_whole_ascii_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> x:ascii_string ->
  Lemma (is_well_formed_whole (ps_whole_ascii_string #bytes) pre x)
  [SMTPat (is_well_formed_whole (ps_whole_ascii_string #bytes) pre x)]

let nat_lbytes_1_is_null (x:nat_lbytes 1) = x = 0
let char_is_null_terminated_ascii (x:FStar.Char.char) = 1 <= FStar.Char.int_of_char x && FStar.Char.int_of_char x < 256
let string_is_null_terminated_ascii (s:string) = List.Tot.for_all char_is_null_terminated_ascii (FStar.String.list_of_string s)
type null_terminated_ascii_string = s:string{normalize_term (b2t (string_is_null_terminated_ascii s))}
let null_terminated_ascii_char_to_byte (c:refined FStar.Char.char char_is_null_terminated_ascii): refined (nat_lbytes 1) (pred_not nat_lbytes_1_is_null) = FStar.Char.int_of_char c

val ps_null_terminated_ascii_string:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer bytes null_terminated_ascii_string

val ps_null_terminated_ascii_string_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:null_terminated_ascii_string ->
  Lemma (
    (ps_null_terminated_ascii_string #bytes).serialize x ==
    List.Tot.fold_right (@) (List.Tot.map #(refined (nat_lbytes 1) (pred_not nat_lbytes_1_is_null)) ((ps_nat_lbytes 1).serialize) (List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string x)))) ((ps_nat_lbytes 1).serialize 0)
  )
  [SMTPat ((ps_null_terminated_ascii_string #bytes).serialize x)]

val ps_null_terminated_ascii_string_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:null_terminated_ascii_string ->
  Lemma (
    prefixes_length ((ps_null_terminated_ascii_string #bytes).serialize x) == FStar.String.strlen x + 1
  )
  [SMTPat (prefixes_length ((ps_null_terminated_ascii_string #bytes).serialize x))]

val ps_null_terminated_ascii_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> x:null_terminated_ascii_string ->
  Lemma (is_well_formed_prefix (ps_null_terminated_ascii_string #bytes) pre x)
  [SMTPat (is_well_formed_prefix (ps_null_terminated_ascii_string #bytes) pre x)]

(*** Parser for variable-length bytes / lists ***)

/// The parsers below work by serializing length first, then the variable-length data.
/// How do we serialize the length? There are several ways to do it, therefore the definitions below depend on a `nat_parser_serializer`.

type pre_length_bytes (bytes:Type0) {|bytes_like bytes|} (pre_length:nat -> bool) = b:bytes{pre_length (length b)}
type pre_length_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (pre_length:nat -> bool) = l:list a{pre_length (bytes_length ps_a l)}
type pre_length_seq (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (pre_length:nat -> bool) = s:Seq.seq a{pre_length (bytes_length ps_a (Seq.seq_to_list s))}


val ps_pre_length_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> pre_length:(nat -> bool) -> nat_parser_serializer bytes pre_length -> parser_serializer bytes (pre_length_bytes bytes pre_length)

val ps_pre_length_bytes_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  x:pre_length_bytes bytes pre_length ->
  Lemma ((ps_pre_length_bytes pre_length ps_length).serialize x == (ps_length.serialize (length #bytes x)) @ [x])
  [SMTPat ((ps_pre_length_bytes pre_length ps_length).serialize x)]

val ps_pre_length_bytes_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  pre:bytes_compatible_pre bytes -> x:pre_length_bytes bytes pre_length ->
  Lemma (is_well_formed_prefix (ps_pre_length_bytes pre_length ps_length) pre x <==> pre x)
  [SMTPat (is_well_formed_prefix (ps_pre_length_bytes pre_length ps_length) pre x)]

val ps_pre_length_bytes_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  x:pre_length_bytes bytes pre_length ->
  Lemma (prefixes_length ((ps_pre_length_bytes pre_length ps_length).serialize x) == (prefixes_length (ps_length.serialize (length #bytes x))) + (length #bytes x))
  [SMTPat (prefixes_length ((ps_pre_length_bytes pre_length ps_length).serialize x))]

val ps_pre_length_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> nat_parser_serializer bytes pre_length -> ps_a:parser_serializer bytes a -> parser_serializer bytes (pre_length_list ps_a pre_length)

val ps_pre_length_list_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  ps_a:parser_serializer bytes a ->
  x:pre_length_list ps_a pre_length ->
  Lemma ((ps_pre_length_list pre_length ps_length ps_a).serialize x == (ps_length.serialize (length ((ps_whole_list ps_a).serialize x))) @ [(ps_whole_list ps_a).serialize x])
  [SMTPat ((ps_pre_length_list pre_length ps_length ps_a).serialize x)]

val ps_pre_length_list_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  ps_a:parser_serializer bytes a ->
  pre:bytes_compatible_pre bytes -> x:pre_length_list ps_a pre_length ->
  Lemma (is_well_formed_prefix (ps_pre_length_list pre_length ps_length ps_a) pre x <==> for_allP (is_well_formed_prefix ps_a pre) x)
  [SMTPat (is_well_formed_prefix (ps_pre_length_list pre_length ps_length ps_a) pre x)]

val ps_pre_length_list_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  ps_a:parser_serializer bytes a ->
  x:pre_length_list ps_a pre_length ->
  Lemma (prefixes_length ((ps_pre_length_list pre_length ps_length ps_a).serialize x) == (prefixes_length (ps_length.serialize (bytes_length ps_a x))) + (bytes_length ps_a x))
  [SMTPat (prefixes_length ((ps_pre_length_list pre_length ps_length ps_a).serialize x))]

val ps_pre_length_seq: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> nat_parser_serializer bytes pre_length -> ps_a:parser_serializer bytes a -> parser_serializer bytes (pre_length_seq ps_a pre_length)

val ps_pre_length_seq_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  ps_a:parser_serializer bytes a ->
  pre:bytes_compatible_pre bytes -> x:pre_length_seq ps_a pre_length ->
  Lemma (is_well_formed_prefix (ps_pre_length_seq pre_length ps_length ps_a) pre x <==> for_allP (is_well_formed_prefix ps_a pre) (Seq.seq_to_list x))
  [SMTPat (is_well_formed_prefix (ps_pre_length_seq pre_length ps_length ps_a) pre x)]

val ps_pre_length_seq_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length ->
  ps_a:parser_serializer bytes a ->
  x:pre_length_seq ps_a pre_length ->
  Lemma (prefixes_length ((ps_pre_length_seq pre_length ps_length ps_a).serialize x) == (prefixes_length (ps_length.serialize (bytes_length ps_a (Seq.seq_to_list x)))) + (bytes_length ps_a (Seq.seq_to_list x)))
  [SMTPat (prefixes_length ((ps_pre_length_seq pre_length ps_length ps_a).serialize x))]

/// Length parser/serializer for TLS-style length in range

type size_range = {
  min: nat;
  max: max:nat{normalize_term min <= normalize_term max};
}

let in_range (r:size_range) (x:nat) =
  r.min <= x && x <= r.max

type tls_nat (r:size_range) = refined nat (in_range r)
val ps_tls_nat:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  r:size_range ->
  nat_parser_serializer bytes (in_range r)

val ps_tls_nat_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  r:size_range ->
  x:tls_nat r ->
  Lemma ((ps_tls_nat #bytes r).serialize x == [from_nat (find_nbytes r.max) x])
  [SMTPat ((ps_tls_nat #bytes r).serialize x)]

val ps_tls_nat_length: #bytes:Type0 -> {|bytes_like bytes|} -> r:size_range -> x:tls_nat r -> Lemma
  (prefixes_length #bytes ((ps_tls_nat r).serialize x) == find_nbytes r.max)
  [SMTPat (prefixes_length #bytes ((ps_tls_nat r).serialize x))]

type tls_bytes (bytes:Type0) {|bytes_like bytes|} (r:size_range) = pre_length_bytes bytes (in_range r)
type tls_list (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (r:size_range) = pre_length_list ps_a (in_range r)
type tls_seq (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (r:size_range) = pre_length_seq ps_a (in_range r)

let ps_tls_bytes (#bytes:Type0) {|bytes_like bytes|} (r:size_range): parser_serializer bytes (tls_bytes bytes r) = ps_pre_length_bytes (in_range r) (ps_tls_nat r)
let ps_tls_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (r:size_range): parser_serializer bytes (tls_list bytes ps_a r) = ps_pre_length_list #bytes (in_range r) (ps_tls_nat r) ps_a
let ps_tls_seq (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (r:size_range): parser_serializer bytes (tls_seq bytes ps_a r) = ps_pre_length_seq #bytes (in_range r) (ps_tls_nat r) ps_a


/// Length parser/serializer for unbounded length. Useful for proofs.
/// For a nat that fit on n bytes, it stores it using 2n+1 bytes, so it is ok-ish compact.

let true_nat_pred (n:nat) = true
type true_nat = refined nat true_nat_pred
val ps_true_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes true_nat_pred

let ps_nat (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes nat =
  mk_trivial_isomorphism ps_true_nat

let ps_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes bytes =
  mk_trivial_isomorphism (ps_pre_length_bytes true_nat_pred ps_true_nat)

let ps_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (list a) =
  mk_trivial_isomorphism (ps_pre_length_list true_nat_pred ps_true_nat ps_a)

let ps_seq (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (Seq.seq a) =
  mk_trivial_isomorphism (ps_pre_length_seq true_nat_pred ps_true_nat ps_a)

/// QUIC-style length

let quic_nat_pred (n:nat) = n < normalize_term (pow2 62)
let quic_nat_pred_eq (n:nat): Lemma(pow2 62 == normalize_term (pow2 62)) [SMTPat (quic_nat_pred n)] =
  assert_norm(pow2 62 == normalize_term (pow2 62))
type quic_nat = refined nat quic_nat_pred
val ps_quic_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes quic_nat_pred

val ps_quic_nat_length: #bytes:Type0 -> {| bytes_like bytes |} -> x:quic_nat -> Lemma (
  prefixes_length #bytes (ps_quic_nat.serialize x) == (
    if x < pow2 6 then 1
    else if x < pow2 14 then 2
    else if x < pow2 30 then 4
    else 8
  ))
  [SMTPat (prefixes_length #bytes (ps_quic_nat.serialize x))]

type quic_bytes (bytes:Type0) {|bytes_like bytes|} = pre_length_bytes bytes quic_nat_pred
type quic_list (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_list ps_a quic_nat_pred
type quic_seq (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_seq ps_a quic_nat_pred

let ps_quic_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes (quic_bytes bytes) = ps_pre_length_bytes quic_nat_pred ps_quic_nat
let ps_quic_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (quic_list bytes ps_a) = ps_pre_length_list #bytes quic_nat_pred ps_quic_nat ps_a
let ps_quic_seq (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (quic_seq bytes ps_a) = ps_pre_length_seq #bytes quic_nat_pred ps_quic_nat ps_a
