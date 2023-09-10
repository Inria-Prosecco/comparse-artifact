module TLS13.CryptoInput

open TLS13.MessageFormats
open Comparse

/// struct {
///     uint16 length = Length;
///     opaque label<7..255> = "tls13 " + Label;
///     opaque context<0..255> = Context;
/// } HkdfLabel;

type hkdf_label (bytes:Type0) {|bytes_like bytes|} = {
  length: nat_lbytes 2;
  label: tls_bytes bytes ({min=7; max=255});
  context: tls_bytes bytes ({min=0; max=255});
}

%splice [ps_hkdf_label] (gen_parser (`hkdf_label))

/// struct {
///     opaque content[TLSPlaintext.length];
///     ContentType type;
///     uint8 zeros[length_of_padding];
/// } TLSInnerPlaintext;

type tls_inner_plaintext (bytes:Type0) {|bytes_like bytes|} = {
  content: bytes;
  ctype: ctype:content_type{ctype <> CT_invalid};
  padding: nat;
}

val content_type_to_nat:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  content_type ->
  nat_lbytes 1
let content_type_to_nat #bytes #bl ctype =
  ps_content_type_serialize #bytes ctype;
  let serialized = ((ps_prefix_to_ps_whole #bytes ps_content_type).serialize ctype) in
  FStar.Classical.forall_intro_2 (from_to_nat #bytes);
  split_concat #bytes (
    match ctype with
    | CT_invalid -> from_nat 1 0
    | CT_change_cipher_spec -> from_nat 1 20
    | CT_alert -> from_nat 1 21
    | CT_handshake -> from_nat 1 22
    | CT_application_data -> from_nat 1 23
    | CT_heartbeat -> from_nat 1 24
  ) empty;
  let Some (lhs, _) = split serialized 1 in
  let Some res = to_nat lhs in
  res

val nat_to_content_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  nat_lbytes 1 ->
  option content_type
let nat_to_content_type #bytes #bl x =
  let b = concat (from_nat 1 x) empty in
  (ps_prefix_to_ps_whole #bytes ps_content_type).parse b

val content_type_to_nat_to_content_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctype:content_type ->
  Lemma (nat_to_content_type #bytes (content_type_to_nat #bytes ctype) == Some ctype)
let content_type_to_nat_to_content_type #bytes #bl ctype =
  (ps_prefix_to_ps_whole #bytes ps_content_type).parse_serialize_inv ctype;
  FStar.Classical.forall_intro_2 (split_concat #bytes);
  FStar.Classical.forall_intro_2 (from_to_nat #bytes)

val nat_to_content_type_to_nat:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  n:nat_lbytes 1 ->
  Lemma (
    match (nat_to_content_type #bytes n) with
    | None -> True
    | Some ctype -> content_type_to_nat #bytes ctype == n
  )
let nat_to_content_type_to_nat #bytes #bl n =
  (ps_prefix_to_ps_whole #bytes ps_content_type).serialize_parse_inv (concat (from_nat 1 n) empty);
  FStar.Classical.forall_intro_2 (split_concat #bytes);
  FStar.Classical.forall_intro_2 (from_to_nat #bytes);
  FStar.Classical.forall_intro_2 (concat_split #bytes);
  FStar.Classical.forall_intro (to_from_nat #bytes)

val content_type_to_nat_zero:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctype:content_type ->
  Lemma
  ((ctype == CT_invalid) <==> (content_type_to_nat #bytes ctype == 0))
let content_type_to_nat_zero #bytes #bl ctype =
  FStar.Classical.forall_intro_2 (split_concat #bytes);
  FStar.Classical.forall_intro_2 (from_to_nat #bytes)

val serialize_tls_inner_plaintext:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:tls_inner_plaintext bytes ->
  Tot bytes (decreases x.padding)
let rec serialize_tls_inner_plaintext #bytes #bl x =
  if x.padding = 0 then
    concat x.content (from_nat 1 (content_type_to_nat #bytes x.ctype))
  else (
    concat (serialize_tls_inner_plaintext ({x with padding = x.padding-1;})) (from_nat 1 0)
  )

val parse_tls_inner_plaintext:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  b:bytes ->
  Tot (option (tls_inner_plaintext bytes)) (decreases length b)
let rec parse_tls_inner_plaintext #bytes #bl b =
  if length b = 0 then None
  else (
    match split #bytes b (length b - 1) with
    | None -> None
    | Some (lhs, rhs) ->
      match to_nat rhs with
      | None -> None
      | Some 0 -> (
        match parse_tls_inner_plaintext lhs with
        | None -> None
        | Some x -> Some {x with padding = x.padding + 1;}
      )
      | Some ctype_n -> (
        match nat_to_content_type #bytes ctype_n with
        | None -> None
        | Some ctype -> (
          if ctype = CT_invalid then (
            nat_to_content_type_to_nat #bytes ctype_n;
            content_type_to_nat_zero #bytes ctype;
            false_elim ()
          ) else (
            Some { content = lhs; ctype; padding = 0; }
          )
        )
      )
  )

val parse_serialize_tls_inner_plaintext:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:tls_inner_plaintext bytes ->
  Lemma
  (ensures parse_tls_inner_plaintext (serialize_tls_inner_plaintext x) == Some x)
  (decreases x.padding)
let rec parse_serialize_tls_inner_plaintext #bytes #bl x =
  if x.padding = 0 then (
    FStar.Classical.forall_intro_2 (from_to_nat #bytes);
    content_type_to_nat_to_content_type #bytes x.ctype;
    content_type_to_nat_zero #bytes x.ctype;
    split_concat #bytes x.content (from_nat 1 (content_type_to_nat #bytes x.ctype))
  ) else (
    FStar.Classical.forall_intro_2 (from_to_nat #bytes);
    FStar.Classical.forall_intro_2 (split_concat #bytes);
    parse_serialize_tls_inner_plaintext {x with padding = x.padding-1;}
  )

val serialize_parse_tls_inner_plaintext:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  b:bytes ->
  Lemma
  (ensures (
    match parse_tls_inner_plaintext b with
    | None -> True
    | Some x -> serialize_tls_inner_plaintext x == b
  ))
  (decreases length b)
let rec serialize_parse_tls_inner_plaintext #bytes #bl b =
  if length b = 0 then ()
  else (
    match split #bytes b (length b - 1) with
    | None -> ()
    | Some (lhs, rhs) ->
      match to_nat rhs with
      | None -> ()
      | Some 0 -> (
        match parse_tls_inner_plaintext lhs with
        | None -> ()
        | Some x -> (
          to_from_nat #bytes rhs;
          concat_split b (length b - 1);
          serialize_parse_tls_inner_plaintext lhs
        )
      )
      | Some ctype_n -> (
        match nat_to_content_type #bytes ctype_n with
        | None -> ()
        | Some ctype -> (
          if ctype = CT_invalid then (
            nat_to_content_type_to_nat #bytes ctype_n;
            content_type_to_nat_zero #bytes ctype;
            assert(False)
          ) else (
            to_from_nat #bytes rhs;
            concat_split b (length b - 1);
            nat_to_content_type_to_nat #bytes ctype_n
          )
        )
      )
  )

val ps_whole_tls_inner_plaintext:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_whole bytes (tls_inner_plaintext bytes)
let ps_whole_tls_inner_plaintext #bytes #bl = {
  parse = parse_tls_inner_plaintext #bytes;
  serialize = serialize_tls_inner_plaintext #bytes;
  parse_serialize_inv = parse_serialize_tls_inner_plaintext #bytes;
  serialize_parse_inv = serialize_parse_tls_inner_plaintext #bytes;
}
