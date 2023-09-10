module CTLS.Profile

open Comparse
open TLS13.MessageFormats

#set-options "--fuel 0 --ifuel 1"

/// enum {
///   profile(0),
///   version(1),
///   cipher_suite(2),
///   dh_group(3),
///   signature_algorithm(4),
///   random(5),
///   mutual_auth(6),
///   handshake_framing(7),
///   client_hello_extensions(8),
///   server_hello_extensions(9),
///   encrypted_extensions(10),
///   certificate_request_extensions(11),
///   known_certificates(12),
///   finished_size(13),
///   optional(65535)
/// } CTLSTemplateElementType;

type ctls_template_element_type =
  | [@@@ with_num_tag 2 (0)]     CTLSTET_profile: ctls_template_element_type
  | [@@@ with_num_tag 2 (1)]     CTLSTET_version: ctls_template_element_type
  | [@@@ with_num_tag 2 (2)]     CTLSTET_cipher_suite: ctls_template_element_type
  | [@@@ with_num_tag 2 (3)]     CTLSTET_dh_group: ctls_template_element_type
  | [@@@ with_num_tag 2 (4)]     CTLSTET_signature_algorithm: ctls_template_element_type
  | [@@@ with_num_tag 2 (5)]     CTLSTET_random: ctls_template_element_type
  | [@@@ with_num_tag 2 (6)]     CTLSTET_mutual_auth: ctls_template_element_type
  | [@@@ with_num_tag 2 (7)]     CTLSTET_handshake_framing: ctls_template_element_type
  | [@@@ with_num_tag 2 (8)]     CTLSTET_client_hello_extensions: ctls_template_element_type
  | [@@@ with_num_tag 2 (9)]     CTLSTET_server_hello_extensions: ctls_template_element_type
  | [@@@ with_num_tag 2 (10)]    CTLSTET_encrypted_extensions: ctls_template_element_type
  | [@@@ with_num_tag 2 (11)]    CTLSTET_certificate_request_extensions: ctls_template_element_type
  | [@@@ with_num_tag 2 (12)]    CTLSTET_known_certificates: ctls_template_element_type
  | [@@@ with_num_tag 2 (13)]    CTLSTET_finished_size: ctls_template_element_type
  | [@@@ with_num_tag 2 (65535)] CTLSTET_optional: ctls_template_element_type

%splice [ps_ctls_template_element_type] (gen_parser (`ctls_template_element_type))

/// struct {
///   CTLSTemplateElementType type;
///   opaque data<0..2^32-1>;
/// } CTLSTemplateElement;

type ctls_template_element (bytes:Type0) {|bytes_like bytes|} = {
  ty: ctls_template_element_type;
  data: tls_bytes bytes (({min=0; max=(pow2 32)-1}));
}

%splice [ps_ctls_template_element] (gen_parser (`ctls_template_element))

/// struct {
///   uint16 ctls_version = 0;
///   CTLSTemplateElement elements<0..2^32-1>
/// } CTLSTemplate;

type ctls_version =
  | [@@@ with_num_tag 2 (0)] CV_ctls_version_0: ctls_version

%splice [ps_ctls_version] (gen_parser (`ctls_version))

type ctls_template (bytes:Type0) {|bytes_like bytes|} = {
  ctls_version: ctls_version;
  elements: tls_list bytes (ps_ctls_template_element) ({min=0; max=(pow2 32)-1});
}

%splice [ps_ctls_template] (gen_parser (`ctls_template))

instance parseable_serializeable_ctls_template (bytes:Type0) {|bytes_like bytes|} : parseable_serializeable bytes (ctls_template bytes) = mk_parseable_serializeable ps_ctls_template

(*** Templates ***)

/// opaque ProfileID<1..2^8-1>

type ctls_profile_template (bytes:Type0) {|bytes_like bytes|} =
  tls_bytes bytes ({min=1; max=(pow2 8)-1})

%splice [ps_ctls_profile_template] (gen_parser (`ctls_profile_template))

/// cipher_suite. Value: a single CipherSuite ([RFC8446], Section 4.1.2) that both parties agree to use.

type ctls_cipher_suite_template (bytes:Type0) {|bytes_like bytes|} =
  cipher_suite

%splice [ps_ctls_cipher_suite_template] (gen_parser (`ctls_cipher_suite_template))

/// dh_group:
/// struct {
///     NamedGroup group_name;
///     uint16 key_share_length;
/// } CTLSKeyShareGroup;

type ctls_dh_group_template (bytes:Type0) {|bytes_like bytes|} = {
  group_name: named_group;
  key_share_length: nat_lbytes 2;
}

%splice [ps_ctls_dh_group_template] (gen_parser (`ctls_dh_group_template))

/// struct {
///     SignatureScheme signature_scheme;
///     uint16 signature_length;
/// } CTLSSignatureAlgorithm;

type ctls_signature_algorithm_template (bytes:Type0) {|bytes_like bytes|} = {
  signature_scheme: signature_scheme;
  signature_length: nat_lbytes 2;
}

%splice [ps_ctls_signature_algorithm_template] (gen_parser (`ctls_signature_algorithm_template))

/// random. Value: a single uint8.
/// The Random length MUST be less than or equal to 32 bytes

val less_than_32: nat_lbytes 1 -> bool
let less_than_32 (x:nat_lbytes 1) = x <= 32

type ctls_random_template (bytes:Type0) {|bytes_like bytes|} =
  refined (nat_lbytes 1) less_than_32

val ps_ctls_random_template: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (ctls_random_template bytes)
let ps_ctls_random_template #bytes #bl =
  refine (ps_nat_lbytes  1) less_than_32

/// mutual_auth. Value: a single uint8, with 1 representing "true" and 0 representing "false". All other values are forbidden.

val bool_pred: nat_lbytes 1 -> bool
let bool_pred x = x = 0 || x = 1

type ctls_mutual_auth_template (bytes:Type0) {|bytes_like bytes|} =
  refined (nat_lbytes 1) bool_pred

val ps_ctls_mutual_auth_template: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (ctls_mutual_auth_template bytes)
let ps_ctls_mutual_auth_template #bytes #bl =
  refine (ps_nat_lbytes 1) bool_pred

/// struct {
///   Extension predefined_extensions<0..2^16-1>;
///   ExtensionType expected_extensions<0..2^16-1>;
///   ExtensionType self_delimiting_extensions<0..2^16-1>;
///   uint8 allow_additional;
/// } CTLSExtensionTemplate;

type ctls_extension_template (bytes:Type0) {|bytes_like bytes|} = {
  predefined_extensions: tls_list bytes (ps_extension) ({min=0; max=(pow2 16)-1});
  expected_extensions: tls_list bytes (ps_extension_type) ({min=0; max=(pow2 16)-1});
  self_delimiting_extensions: tls_list bytes (ps_extension_type) ({min=0; max=(pow2 16)-1});
  allow_additional: nat_lbytes 1;
}

%splice [ps_ctls_extension_template] (gen_parser (`ctls_extension_template))

/// finished_size. Value: uint8, indicating that the Finished value is to be truncated to the given length.

type ctls_finished_template (bytes:Type0) {|bytes_like bytes|} =
  nat_lbytes 1

%splice [ps_ctls_finished_template] (gen_parser (`ctls_finished_template))

/// handshake_framing. Value: uint8, with 0 indicating "false" and 1 indicating "true".

type ctls_handshake_framing_template (bytes:Type0) {|bytes_like bytes|} =
  refined (nat_lbytes 1) bool_pred

val ps_ctls_handshake_framing_template: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (ctls_handshake_framing_template bytes)
let ps_ctls_handshake_framing_template #bytes #bl =
  refine (ps_nat_lbytes 1) bool_pred

/// optional. Value: a CTLSTemplate containing elements that are not required to be understood by the client.

type ctls_optional_template (bytes:Type0) {|bytes_like bytes|} =
  ctls_template bytes

%splice [ps_ctls_optional_template] (gen_parser (`ctls_optional_template))

/// struct {
///   opaque id<1..2^8-1>;
///   opaque cert_data<1..2^16-1>;
/// } CertificateMapEntry;

type certificate_map_entry (bytes:Type0) {|bytes_like bytes|} = {
  id: tls_bytes bytes (({min=1; max=(pow2 8)-1}));
  cert_data: tls_bytes bytes (({min=1; max=(pow2 16)-1}));
}

%splice [ps_certificate_map_entry] (gen_parser (`certificate_map_entry))

/// struct {
///   CertificateMapEntry entries<2..2^24-1>;
/// } CertificateMap;

type certificate_map (bytes:Type0) {|bytes_like bytes|} = {
  entries: tls_list bytes (ps_certificate_map_entry) ({min=2; max=(pow2 24)-1});
}

%splice [ps_certificate_map] (gen_parser (`certificate_map))

(*** Utility function ***)

val get_template_element_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  parser_serializer bytes a -> ctls_template_element_type -> list (ctls_template_element bytes) ->
  option a
let rec get_template_element_aux #bytes #bl #a ps_a ty l =
  match l with
  | [] -> None
  | h::t ->
    if h.ty = ty then
      (ps_prefix_to_ps_whole ps_a).parse h.data
    else
      get_template_element_aux ps_a ty t

val get_template_element:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  parser_serializer bytes a -> ctls_template_element_type -> ctls_template bytes ->
  option a
let get_template_element #bytes #bl #a ps_a ty template =
  get_template_element_aux ps_a ty template.elements
