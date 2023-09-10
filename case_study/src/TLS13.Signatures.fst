module TLS13.Signatures

open FStar.List.Tot
open Comparse

#set-options "--fuel 0 --ifuel 0"

(*** TLS 1.3 signatures ***)

/// The digital signature is then computed over the concatenation of:
///
/// -  A string that consists of octet 32 (0x20) repeated 64 times
/// -  The context string
/// -  A single 0 byte which serves as the separator
/// -  The content to be signed
///
/// ...
///
/// The context string for a server signature is
/// "TLS 1.3, server CertificateVerify".  The context string for a
/// client signature is "TLS 1.3, client CertificateVerify".  It is
/// used to provide separation between signatures made in different
/// contexts, helping against potential cross-protocol attacks.
/// For example, if the transcript hash was 32 bytes of 01 (this length
/// would make sense for SHA-256), the content covered by the digital
/// signature for a server CertificateVerify would be:
///
///    2020202020202020202020202020202020202020202020202020202020202020
///    2020202020202020202020202020202020202020202020202020202020202020
///    544c5320312e332c207365727665722043657274696669636174655665726966
///    79
///    00
///    0101010101010101010101010101010101010101010101010101010101010101

val is_equal_to_fake_random: nat_lbytes 32 -> bool
let is_equal_to_fake_random n =
  n = 0x2020202020202020202020202020202020202020202020202020202020202020

type tls13_sigval_fake_random = refined (nat_lbytes 32) is_equal_to_fake_random

val ps_tls13_sigval_fake_random: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes tls13_sigval_fake_random
let ps_tls13_sigval_fake_random #bytes #bl = refine (ps_nat_lbytes 32) is_equal_to_fake_random

let tls13_server_label: null_terminated_ascii_string = "TLS 1.3, server CertificateVerify"
let tls13_client_label: null_terminated_ascii_string = "TLS 1.3, client CertificateVerify"

let tls13_label_prefix = "TLS 1.3, "

// There is bad equational theory on FStar.String.sub, hence this weird `is_prefix_of` definition
val is_prefix_of:
  pref:string -> string -> i:nat ->
  Tot bool (decreases (FStar.String.strlen pref - i))
let rec is_prefix_of pref s i =
  if not (FStar.String.strlen pref <= FStar.String.strlen s) then
    false
  else if not (i < FStar.String.strlen pref) then
    true
  else (
    FStar.String.index pref i = FStar.String.index s i &&
    is_prefix_of pref s (i+1)
  )

// Sanity check
let _ = assert_norm (is_prefix_of tls13_label_prefix tls13_server_label 0)
let _ = assert_norm (is_prefix_of tls13_label_prefix tls13_client_label 0)

val is_equal_to_server_label: null_terminated_ascii_string -> bool
let is_equal_to_server_label s = is_prefix_of tls13_label_prefix s 0

type tls13_sigval_server_label = refined null_terminated_ascii_string is_equal_to_server_label

val ps_tls13_sigval_server_label:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer bytes tls13_sigval_server_label
let ps_tls13_sigval_server_label #bytes #bl =
  refine ps_null_terminated_ascii_string is_equal_to_server_label

type tls13_sigval_label = {
  fake_client_random: tls13_sigval_fake_random;
  fake_server_random: tls13_sigval_fake_random;
  server_label: tls13_sigval_server_label;
}

%splice [ps_tls13_sigval_label] (gen_parser (`tls13_sigval_label))
%splice [ps_tls13_sigval_label_serialize] (gen_serialize_lemma (`tls13_sigval_label))

type tls13_sigval (bytes:Type0) {|bytes_like bytes|} = {
  label: tls13_sigval_label;
  content: bytes;
}

val ps_whole_tls13_sigval: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer_whole bytes (tls13_sigval bytes)
let ps_whole_tls13_sigval #bytes #bl =
  mk_isomorphism_whole (tls13_sigval bytes)
    (bind_whole ps_tls13_sigval_label (fun _ -> ps_whole_bytes))
    (fun (|label, content|) -> {label; content;})
    (fun {label; content;} -> (|label, content|))

instance parseable_serializeable_tls13_sigval (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (tls13_sigval bytes) =
  mk_parseable_serializeable_from_whole ps_whole_tls13_sigval

#push-options "--ifuel 1"
val ps_whole_tls13_sigval_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sv13:tls13_sigval bytes ->
  Lemma ((serialize _ sv13 <: bytes) ==
    concat #bytes (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) (
      concat (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) (
        add_prefixes (ps_null_terminated_ascii_string.serialize sv13.label.server_label) (
          sv13.content
        )
      )
    )
  )
let ps_whole_tls13_sigval_serialize #bytes #bl sv13 =
  let the_list: list bytes =
    [from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020] @ (
      [from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020] @ (
        (ps_null_terminated_ascii_string.serialize sv13.label.server_label)
      )
    )
  in
  assert((serialize _ sv13 <: bytes) == add_prefixes the_list sv13.content);
  assert_norm(add_prefixes the_list sv13.content == (
    concat #bytes (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) (
      concat (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) (
        add_prefixes (ps_null_terminated_ascii_string.serialize sv13.label.server_label) (
          sv13.content
        )
      )
    )
  ))
#pop-options

(*** TLS 1.2 Server FFDHE Signature ***)

/// struct {
///     opaque dh_p<1..2^16-1>;
///     opaque dh_g<1..2^16-1>;
///     opaque dh_Ys<1..2^16-1>;
/// } ServerDHParams;     /* Ephemeral DH parameters */

type server_dh_params (bytes:Type0) {|bytes_like bytes|} = {
  dh_p: tls_bytes bytes ({min=1; max=(pow2 16)-1});
  dh_g: tls_bytes bytes ({min=1; max=(pow2 16)-1});
  dh_Ys: tls_bytes bytes ({min=1; max=(pow2 16)-1});
}

%splice [ps_server_dh_params] (gen_parser (`server_dh_params))
%splice [ps_server_dh_params_serialize] (gen_serialize_lemma (`server_dh_params))

/// digitally-signed struct {
///     opaque client_random[32];
///     opaque server_random[32];
///     ServerDHParams params;
/// } signed_params;

type tls12_server_dh_sigval (bytes:Type0) {|bytes_like bytes|} = {
  client_random: lbytes bytes 32;
  server_random: lbytes bytes 32;
  params: server_dh_params bytes;
}

%splice [ps_tls12_server_dh_sigval] (gen_parser (`tls12_server_dh_sigval))
%splice [ps_tls12_server_dh_sigval_serialize] (gen_serialize_lemma (`tls12_server_dh_sigval))

instance parseable_serializeable_tls12_server_dh_sigval (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (tls12_server_dh_sigval bytes) =
  mk_parseable_serializeable ps_tls12_server_dh_sigval

#push-options "--fuel 2"
val serialize_tls12_server_dh_sigval:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sv12:tls12_server_dh_sigval bytes ->
  Lemma ((serialize _ sv12 <: bytes) ==
    concat sv12.client_random (
      concat sv12.server_random (
        concat (from_nat 2 (length (sv12.params.dh_p <: bytes))) (
          concat sv12.params.dh_p (
            concat (from_nat 2 (length (sv12.params.dh_g <: bytes))) (
              concat sv12.params.dh_g (
                concat (from_nat 2 (length (sv12.params.dh_Ys <: bytes))) (
                  concat sv12.params.dh_Ys (
                    empty #bytes
                  )
                )
              )
            )
          )
        )
      )
    )
  )
let serialize_tls12_server_dh_sigval #bytes #bl sv12 =
  let the_list: list bytes =
    [sv12.client_random] @ (
      [sv12.server_random] @ (
        ([from_nat 2 (length (sv12.params.dh_p <: bytes))] @ [sv12.params.dh_p]) @ (
          ([from_nat 2 (length (sv12.params.dh_g <: bytes))] @ [sv12.params.dh_g]) @ (
            ([from_nat 2 (length (sv12.params.dh_Ys <: bytes))] @ [sv12.params.dh_Ys])
          )
        )
      )
    )
  in
  assert((serialize _ sv12 <: bytes) == add_prefixes the_list empty);
  normalize_term_spec (add_prefixes the_list empty)
#pop-options

(*** TLS 1.2 ECDHE Server Signature ***)

/// enum {
///     deprecated(1..22),
///     secp256r1 (23), secp384r1 (24), secp521r1 (25),
///     x25519(29), x448(30),
///     reserved (0xFE00..0xFEFF),
///     deprecated(0xFF01..0xFF02),
///     (0xFFFF)
/// } NamedCurve;

type named_curve =
  | [@@@ with_num_tag 2 23] NC_secp256r1: named_curve
  | [@@@ with_num_tag 2 24] NC_secp384r1: named_curve
  | [@@@ with_num_tag 2 25] NC_secp521r1: named_curve
  | [@@@ with_num_tag 2 29] NC_x25519: named_curve
  | [@@@ with_num_tag 2 30] NC_x448: named_curve
  | [@@@ open_tag] NC_unknown:
    n:nat_lbytes 2{
      not (
        (23 <= n  && n <= 25) ||
        (29 <= n  && n <= 30)
      )
    } ->
    named_curve

#push-options "--ifuel 1"
%splice [ps_named_curve] (gen_parser (`named_curve))
#pop-options

/// enum {
///     deprecated (1..2),
///     named_curve (3),
///     reserved(248..255)
/// } ECCurveType;
///
/// struct {
///     ECCurveType    curve_type;
///     select (curve_type) {
///         case named_curve:
///             NamedCurve namedcurve;
///     };
/// } ECParameters;

type ec_parameters =
  | [@@@ with_num_tag 1 3] ECP_named_curve: namedcurve: named_curve -> ec_parameters

#push-options "--ifuel 1"
%splice [ps_ec_parameters] (gen_parser (`ec_parameters))
%splice [ps_ec_parameters_serialize] (gen_serialize_lemma (`ec_parameters))
#pop-options

/// struct {
///     opaque point <1..2^8-1>;
/// } ECPoint;

type ec_point (bytes:Type0) {|bytes_like bytes|} =
  tls_bytes bytes {min=1; max=(pow2 8)-1;}

%splice [ps_ec_point] (gen_parser (`ec_point))

/// struct {
///     ECParameters    curve_params;
///     ECPoint         public;
/// } ServerECDHParams;

type server_ecdh_params (bytes:Type0) {|bytes_like bytes|} = {
  curve_params: ec_parameters;
  public: ec_point bytes;
}

%splice [ps_server_ecdh_params] (gen_parser (`server_ecdh_params))
%splice [ps_server_ecdh_params_serialize] (gen_serialize_lemma (`server_ecdh_params))

/// digitally-signed struct {
///     opaque rawdata[rawdata_size];
/// };
///  ServerKeyExchange.signed_params.rawdata =
///      ClientHello.random + ServerHello.random +
///                             ServerKeyExchange.params;

type tls12_server_ecdh_sigval (bytes:Type0) {|bytes_like bytes|} = {
  client_random: lbytes bytes 32;
  server_random: lbytes bytes 32;
  params: server_ecdh_params bytes;
}

%splice [ps_tls12_server_ecdh_sigval] (gen_parser (`tls12_server_ecdh_sigval))
%splice [ps_tls12_server_ecdh_sigval_serialize] (gen_serialize_lemma (`tls12_server_ecdh_sigval))

instance parseable_serializeable_tls12_server_ecdh_sigval (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (tls12_server_ecdh_sigval bytes) =
  mk_parseable_serializeable ps_tls12_server_ecdh_sigval

val serialize_tls12_server_ecdh_sigval:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sv12:tls12_server_ecdh_sigval bytes ->
  Lemma ((serialize _ sv12 <: bytes) ==
    concat sv12.client_random (
      concat sv12.server_random (
        concat (from_nat 1 3) (
          add_prefixes (
            (ps_named_curve.serialize (ECP_named_curve?.namedcurve sv12.params.curve_params)) @
            (ps_ec_point.serialize sv12.params.public)
          ) (empty #bytes)
        )
      )
    )
  )
let serialize_tls12_server_ecdh_sigval #bytes #bl sv12 =
  let the_list: list bytes =
    [sv12.client_random] @ (
      [sv12.server_random] @ (
        ([from_nat 1 3] @ (ps_named_curve.serialize (ECP_named_curve?.namedcurve sv12.params.curve_params))) @ (
          (ps_ec_point.serialize sv12.params.public)
        )
      )
    )
  in
  assert((serialize _ sv12 <: bytes) == add_prefixes the_list empty);
  assert_norm(add_prefixes the_list empty ==
    concat #bytes sv12.client_random (
      concat sv12.server_random (
        concat (from_nat 1 3) (
          add_prefixes (
            (ps_named_curve.serialize (ECP_named_curve?.namedcurve sv12.params.curve_params)) @
            (ps_ec_point.serialize sv12.params.public)
          ) (empty #bytes)
        )
      )
    )
  )

(*** TLS 1.2 Client Signature ***)

/// struct {
///     HandshakeType msg_type;    /* handshake type */
///     uint24 length;             /* bytes in message */
///     select (HandshakeType) {
///         case hello_request:       HelloRequest;
///         case client_hello:        ClientHello;
///         case server_hello:        ServerHello;
///         case certificate:         Certificate;
///         case server_key_exchange: ServerKeyExchange;
///         case certificate_request: CertificateRequest;
///         case server_hello_done:   ServerHelloDone;
///         case certificate_verify:  CertificateVerify;
///         case client_key_exchange: ClientKeyExchange;
///         case finished:            Finished;
///     } body;
/// } Handshake;

// The TLS 1.2 handshake is slightly different than the one of TLS 1.3
// To prove the non-ambiguity we want, this more general is sufficient.
// More general, because all TLS 1.2 Handshakes can be represented in this type,
// However this type can't always be converted to TLS 1.2 Handshakes:
// it is an over-approximation, which is good to prove non-ambiguity theorems.

type tls12_handshake (bytes:Type0) {|bytes_like bytes|} = {
  msg_type: nat_lbytes 1;
  length: nat_lbytes 3;
  body: lbytes bytes length;
}

%splice [ps_tls12_handshake] (gen_parser (`tls12_handshake))
%splice [ps_tls12_handshake_serialize] (gen_serialize_lemma (`tls12_handshake))

/// digitally-signed struct {
///     opaque handshake_messages[handshake_messages_length];
/// }

type tls12_client_sigval (bytes:Type0) {|bytes_like bytes|} =
  list (tls12_handshake bytes)

val ps_tls12_client_sigval:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_whole bytes (tls12_client_sigval bytes)
let ps_tls12_client_sigval #bytes #bl =
  ps_whole_list ps_tls12_handshake

instance parseable_serializeable_tls12_client_sigval (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (tls12_client_sigval bytes) =
  mk_parseable_serializeable_from_whole ps_tls12_client_sigval

#push-options "--ifuel 1 --fuel 1"
val serialize_tls12_client_sigval:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sv12:tls12_client_sigval bytes ->
  Lemma ((serialize _ sv12 <: bytes) == (
    match sv12 with
    | [] -> empty #bytes
    | h::t -> (
      concat (from_nat 1 h.msg_type) (
        concat (from_nat 3 h.length) (
          concat (h.body) (
            serialize #bytes _ t
          )
        )
      )
    )
  ))
let serialize_tls12_client_sigval #bytes #bl sv12 =
  ps_whole_list_serialize (ps_tls12_handshake #bytes) sv12;
  match sv12 with
  | [] -> ()
  | h::t -> (
    let the_list: list bytes =
      [from_nat 1 h.msg_type] @ (
        [from_nat 3 h.length] @ (
          [h.body]
        )
      )
    in
    assert((serialize _ sv12 <: bytes) == add_prefixes the_list (serialize #bytes _ t));
    assert_norm(add_prefixes the_list (serialize #bytes _ t) ==
      concat (from_nat 1 h.msg_type) (
        concat (from_nat 3 h.length) (
          concat (h.body) (
            serialize #bytes _ t
          )
        )
      )
    )
  )
#pop-options

(*** Non-ambiguity with TLS 1.2 FFDHE Server ***)

type concrete_bytes = (Seq.seq UInt8.t)
instance concrete_bytes_bytes_like = seq_u8_bytes_like

//val seq_length_ps_whole_ascii_string:
//  s:ascii_string ->
//  Lemma (Seq.length ((ps_whole_ascii_string #concrete_bytes).serialize s) == String.length s)
//  [SMTPat (Seq.length ((ps_whole_ascii_string #concrete_bytes).serialize s))]
//let seq_length_ps_whole_ascii_string s =
//  assert(Seq.length ((ps_whole_ascii_string #concrete_bytes).serialize s) == length ((ps_whole_ascii_string #concrete_bytes).serialize s))

let mk_byte (n:nat_lbytes 1) = Seq.create 1 (FStar.UInt8.uint_to_t n)

val from_nat_1_eq: n:nat_lbytes 1 ->
  Lemma (from_nat #concrete_bytes 1 n == mk_byte n)
  [SMTPat (from_nat #concrete_bytes 1 n)]
let from_nat_1_eq n =
  FStar.Endianness.reveal_be_to_n Seq.empty;
  FStar.Endianness.reveal_be_to_n (mk_byte n);
  FStar.Endianness.n_to_be_be_to_n 1 (mk_byte n)

val from_nat_2_eq: n:nat_lbytes 2 -> a:nat_lbytes 1 -> b:nat_lbytes 1 ->
  Lemma
  (requires
    Seq.index (from_nat #concrete_bytes 2 n) 0 == FStar.UInt8.uint_to_t a /\
    Seq.index (from_nat #concrete_bytes 2 n) 1 == FStar.UInt8.uint_to_t b
  )
  (ensures n == 256 `op_Multiply` a + b)
let from_nat_2_eq n a b =
  let buf = Seq.append (Seq.create 1 (FStar.UInt8.uint_to_t a)) (Seq.create 1 (FStar.UInt8.uint_to_t b)) in
  assert((FStar.Endianness.n_to_be 2 n) `Seq.eq` buf);
  FStar.Endianness.reveal_be_to_n buf;
  FStar.Endianness.reveal_be_to_n (Seq.slice buf 0 1);
  FStar.Endianness.reveal_be_to_n Seq.empty

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (length (add_prefixes l suffix) == prefixes_length l + length suffix)
  [SMTPat (length (add_prefixes #bytes l suffix))]
let rec add_prefixes_length #bytes #bl l suffix =
  reveal_opaque (`%prefixes_length) (prefixes_length #bytes);
  match l with
  | [] -> ()
  | h::t ->
    add_prefixes_length t suffix;
    concat_length h (add_prefixes t suffix)
#pop-options


#push-options "--fuel 2 --ifuel 2"
val seq_index_ps_null_terminated_ascii_string_serialize:
  s:null_terminated_ascii_string -> suffix:concrete_bytes -> i:nat ->
  Lemma
  (requires i < FStar.String.strlen s + 1 + Seq.length suffix)
  (ensures (
    assert(length (add_prefixes ((ps_null_terminated_ascii_string #concrete_bytes).serialize s) suffix) == FStar.String.strlen s + 1 + length suffix);
    (i < FStar.String.strlen s ==> FStar.Char.int_of_char (FStar.String.index s i) < 256) /\
    Seq.index (add_prefixes ((ps_null_terminated_ascii_string #concrete_bytes).serialize s) suffix) i == (
      if i < FStar.String.strlen s then
        FStar.UInt8.uint_to_t (FStar.Char.int_of_char (FStar.String.index s i))
      else if i = FStar.String.strlen s then
        FStar.UInt8.uint_to_t 0
      else
        Seq.index suffix (i - (FStar.String.strlen s + 1))
    )
  ))

  (decreases String.strlen s)
  [SMTPat (Seq.index (add_prefixes ((ps_null_terminated_ascii_string #concrete_bytes).serialize s) suffix) i)]
let rec seq_index_ps_null_terminated_ascii_string_serialize s suffix i =
  assert(length (add_prefixes ((ps_null_terminated_ascii_string #concrete_bytes).serialize s) suffix) == FStar.String.strlen s + 1 + length suffix);
  assert(add_prefixes ((ps_null_terminated_ascii_string #concrete_bytes).serialize s) suffix == (
    add_prefixes (List.Tot.fold_right (@) (List.Tot.map #(refined (nat_lbytes 1) (pred_not nat_lbytes_1_is_null)) ((ps_nat_lbytes 1).serialize) (List.Tot.map null_terminated_ascii_char_to_byte (List.Tot.list_refb #_ #char_is_null_terminated_ascii (FStar.String.list_of_string s)))) ((ps_nat_lbytes 1).serialize 0)) suffix
  ));
  match String.list_of_string s with
  | [] -> ()
  | h::t -> (
    if i = 0 then (
      String.index_list_of_string s 0
    ) else (
      if i < String.strlen s then(
        String.index_string_of_list t (i-1);
        String.index_list_of_string s i
      );
      String.list_of_string_of_list t;
      seq_index_ps_null_terminated_ascii_string_serialize (String.string_of_list t) suffix (i-1)
  )
  )
#pop-options

#push-options "--fuel 2"
val server_ffdhe_non_ambiguity_lemma:
  sv12:tls12_server_dh_sigval concrete_bytes ->
  sv13:tls13_sigval concrete_bytes ->
  Lemma
  (requires (serialize _ sv12 <: concrete_bytes) == serialize _ sv13)
  (ensures 32 + 32 + 2 + 0x544c + 2 + 1 + 2 + 1 <= length (serialize _ sv12 <: concrete_bytes))
let server_ffdhe_non_ambiguity_lemma sv12 sv13 =
  assert_norm(String.strlen tls13_label_prefix >= 2);
  serialize_tls12_server_dh_sigval sv12;
  ps_whole_tls13_sigval_serialize sv13;
  let meh: concrete_bytes = (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) in
  assert_norm((FStar.Char.int_of_char (FStar.String.index tls13_label_prefix 0)) == 0x54);
  assert_norm((FStar.Char.int_of_char (FStar.String.index tls13_label_prefix 1)) == 0x4c);
  assert(is_prefix_of tls13_label_prefix sv13.label.server_label 0);
  assert((FStar.Char.int_of_char (FStar.String.index sv13.label.server_label 0)) == 0x54);
  assert((FStar.Char.int_of_char (FStar.String.index sv13.label.server_label 1)) == 0x4c);
  assert(Seq.index (serialize _ sv13 <: concrete_bytes) 64 == FStar.UInt8.uint_to_t 0x54);
  assert(Seq.index (serialize _ sv13 <: concrete_bytes) 65 == FStar.UInt8.uint_to_t 0x4c);
  from_nat_2_eq (length (sv12.params.dh_p <: concrete_bytes)) 0x54 0x4c
#pop-options

#push-options "--ifuel 1"
val server_ffdhe_non_ambiguity_theorem:
  b:concrete_bytes ->
  Lemma
  (requires length b < 21652)
  (ensures parse (tls12_server_dh_sigval concrete_bytes) b == None \/ parse (tls13_sigval concrete_bytes) b == None)
let server_ffdhe_non_ambiguity_theorem b =
  match parse (tls12_server_dh_sigval concrete_bytes) b, parse (tls13_sigval concrete_bytes) b with
  | Some sv12, Some sv13 -> (
    serialize_parse_inv_lemma (tls12_server_dh_sigval concrete_bytes) b;
    serialize_parse_inv_lemma (tls13_sigval concrete_bytes) b;
    server_ffdhe_non_ambiguity_lemma sv12 sv13;
    assert(False)
  )
  | _, _ -> ()
#pop-options

(*** Non-ambiguity with TLS 1.2 ECDHE Server ***)

#push-options "--fuel 1"
val server_ecdhe_non_ambiguity_lemma:
  sv12:tls12_server_ecdh_sigval concrete_bytes ->
  sv13:tls13_sigval concrete_bytes ->
  Lemma
  (requires (serialize _ sv12 <: concrete_bytes) == serialize _ sv13)
  (ensures False)
let server_ecdhe_non_ambiguity_lemma sv12 sv13 =
  assert_norm(String.strlen tls13_label_prefix >= 2);
  serialize_tls12_server_ecdh_sigval sv12;
  ps_whole_tls13_sigval_serialize sv13;
  let meh: concrete_bytes = (from_nat 32 0x2020202020202020202020202020202020202020202020202020202020202020) in
  assert_norm((FStar.Char.int_of_char (FStar.String.index tls13_label_prefix 0)) == 0x54);
  assert(Seq.index (serialize _ sv13 <: concrete_bytes) 64 == FStar.UInt8.uint_to_t 0x54);
  assert(Seq.index (serialize _ sv12 <: concrete_bytes) 64 == FStar.UInt8.uint_to_t 3)
#pop-options

#push-options "--ifuel 1"
val server_ecdhe_non_ambiguity_theorem:
  b:concrete_bytes ->
  Lemma
  (parse (tls12_server_ecdh_sigval concrete_bytes) b == None \/ parse (tls13_sigval concrete_bytes) b == None)
let server_ecdhe_non_ambiguity_theorem b =
  match parse (tls12_server_ecdh_sigval concrete_bytes) b, parse (tls13_sigval concrete_bytes) b with
  | Some sv12, Some sv13 -> (
    serialize_parse_inv_lemma (tls12_server_ecdh_sigval concrete_bytes) b;
    serialize_parse_inv_lemma (tls13_sigval concrete_bytes) b;
    server_ecdhe_non_ambiguity_lemma sv12 sv13;
    assert(False)
  )
  | _, _ -> ()
#pop-options

(*** Non-ambiguity with TLS 1.2 Client ***)

val from_nat_3_eq: n:nat_lbytes 3 -> a:nat_lbytes 1 -> b:nat_lbytes 1 -> c:nat_lbytes 1 ->
  Lemma
  (requires
    Seq.index (from_nat #concrete_bytes 3 n) 0 == FStar.UInt8.uint_to_t a /\
    Seq.index (from_nat #concrete_bytes 3 n) 1 == FStar.UInt8.uint_to_t b /\
    Seq.index (from_nat #concrete_bytes 3 n) 2 == FStar.UInt8.uint_to_t c
  )
  (ensures n == 65536 `op_Multiply` a + 256 `op_Multiply` b + c)
let from_nat_3_eq n a b c =
  let buf = Seq.append (Seq.append (Seq.create 1 (FStar.UInt8.uint_to_t a)) (Seq.create 1 (FStar.UInt8.uint_to_t b))) ((Seq.create 1 (FStar.UInt8.uint_to_t c))) in
  assert((FStar.Endianness.n_to_be 3 n) `Seq.eq` buf);
  FStar.Endianness.reveal_be_to_n buf;
  FStar.Endianness.reveal_be_to_n (Seq.slice buf 0 2);
  FStar.Endianness.reveal_be_to_n (Seq.slice buf 0 1);
  FStar.Endianness.reveal_be_to_n Seq.empty

val mk_fake_random: nat -> nat
let rec mk_fake_random n =
  if n = 0 then 0
  else 0x20 + 256 `op_Multiply` (mk_fake_random (n-1))

#push-options "--fuel 1"
val mk_fake_random_from_seq:
  n:nat ->
  Lemma (mk_fake_random n == FStar.Endianness.be_to_n (Seq.create n (FStar.UInt8.uint_to_t 0x20)))
let rec mk_fake_random_from_seq n =
  let the_seq = Seq.create n (FStar.UInt8.uint_to_t 0x20) in
  FStar.Endianness.reveal_be_to_n the_seq;
  if n = 0 then ()
  else (
    assert((Seq.create (n-1) (FStar.UInt8.uint_to_t 0x20)) `Seq.eq` (Seq.slice the_seq 0 (n-1)));
    mk_fake_random_from_seq (n-1)
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val client_non_ambiguity_lemma:
  sv12:tls12_client_sigval concrete_bytes ->
  sv13:tls13_sigval concrete_bytes ->
  Lemma
  (requires (serialize _ sv12 <: concrete_bytes) == serialize _ sv13)
  (ensures 1 + 3 + 0x202020  <= length (serialize _ sv12 <: concrete_bytes))
let client_non_ambiguity_lemma sv12 sv13 =
  let open FStar.Endianness in
  serialize_tls12_client_sigval sv12;
  ps_whole_tls13_sigval_serialize sv13;
  assert_norm(mk_fake_random 32 == 0x2020202020202020202020202020202020202020202020202020202020202020);
  mk_fake_random_from_seq 32;
  assert(Seq.index (serialize _ sv12 <: concrete_bytes) 1 == FStar.UInt8.uint_to_t 0x20);
  assert(Seq.index (serialize _ sv12 <: concrete_bytes) 2 == FStar.UInt8.uint_to_t 0x20);
  assert(Seq.index (serialize _ sv12 <: concrete_bytes) 3 == FStar.UInt8.uint_to_t 0x20);
  from_nat_3_eq ((hd sv12).length) 0x20 0x20 0x20
#pop-options

#push-options "--ifuel 1"
val client_non_ambiguity_theorem:
  b:concrete_bytes ->
  Lemma
  (requires length b < 2105380)
  (ensures parse (tls12_client_sigval concrete_bytes) b == None \/ parse (tls13_sigval concrete_bytes) b == None)
let client_non_ambiguity_theorem b =
  match parse (tls12_client_sigval concrete_bytes) b, parse (tls13_sigval concrete_bytes) b with
  | Some sv12, Some sv13 -> (
    serialize_parse_inv_lemma (tls12_client_sigval concrete_bytes) b;
    serialize_parse_inv_lemma (tls13_sigval concrete_bytes) b;
    client_non_ambiguity_lemma sv12 sv13;
    assert(False)
  )
  | _, _ -> ()
#pop-options

(*** Final theorem ***)

type tls12_sigval_type =
  | TLS12_SVT_client: tls12_sigval_type
  | TLS12_SVT_server_dh: tls12_sigval_type
  | TLS12_SVT_server_ecdh: tls12_sigval_type

#push-options "--ifuel 1"
let tls12_sigval (bytes:Type0) {|bytes_like bytes|} (ty:tls12_sigval_type): Type0 =
  match ty with
  | TLS12_SVT_client -> tls12_client_sigval bytes
  | TLS12_SVT_server_dh -> tls12_server_dh_sigval bytes
  | TLS12_SVT_server_ecdh -> tls12_server_ecdh_sigval bytes
#pop-options

#push-options "--ifuel 1"
instance parseable_serializeable_tls12_sigval (bytes:Type0) {|bytes_like bytes|} (ty:tls12_sigval_type): parseable_serializeable bytes (tls12_sigval bytes ty) =
  match ty with
  | TLS12_SVT_client -> mk_parseable_serializeable_from_whole ps_tls12_client_sigval
  | TLS12_SVT_server_dh -> mk_parseable_serializeable ps_tls12_server_dh_sigval
  | TLS12_SVT_server_ecdh -> mk_parseable_serializeable ps_tls12_server_ecdh_sigval
#pop-options

#push-options "--ifuel 1"
val non_ambiguity_theorem:
  ty:tls12_sigval_type -> b:concrete_bytes ->
  Lemma
  (requires length b < 21652)
  (ensures parse (tls12_sigval concrete_bytes ty) b == None \/ parse (tls13_sigval concrete_bytes) b == None)
let non_ambiguity_theorem ty b =
  match ty with
  | TLS12_SVT_client -> client_non_ambiguity_theorem b
  | TLS12_SVT_server_dh -> server_ffdhe_non_ambiguity_theorem b
  | TLS12_SVT_server_ecdh -> server_ecdhe_non_ambiguity_theorem b
#pop-options
