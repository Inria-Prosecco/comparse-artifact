module TLS13.MessageFormats

open Comparse

#set-options "--fuel 0 --ifuel 1 --z3rlimit 50"

val pow2_values: x:nat -> Lemma (
  match x with
  | 8 -> pow2 8 == normalize_term (pow2 8)
  | 16 -> pow2 16 == normalize_term (pow2 16)
  | 24 -> pow2 24 == normalize_term (pow2 24)
  | 32 -> pow2 32 == normalize_term (pow2 32)
  | _ -> True
)
  [SMTPat (pow2 x)]
let pow2_values x =
  normalize_term_spec (pow2 8);
  normalize_term_spec (pow2 16);
  normalize_term_spec (pow2 24);
  normalize_term_spec (pow2 32)

/// enum {
///     invalid(0),
///     change_cipher_spec(20),
///     alert(21),
///     handshake(22),
///     application_data(23),
///     heartbeat(24),  /* RFC 6520 */
///     (255)
/// } ContentType;

type content_type =
  | [@@@ with_num_tag 1 (0)]  CT_invalid: content_type
  | [@@@ with_num_tag 1 (20)] CT_change_cipher_spec: content_type
  | [@@@ with_num_tag 1 (21)] CT_alert: content_type
  | [@@@ with_num_tag 1 (22)] CT_handshake: content_type
  | [@@@ with_num_tag 1 (23)] CT_application_data: content_type
  | [@@@ with_num_tag 1 (24)] CT_heartbeat: content_type


%splice [ps_content_type] (gen_parser_with_smt (`content_type))
%splice [ps_content_type_serialize] (gen_serialize_lemma (`content_type))


/// enum { warning(1), fatal(2), (255) } AlertLevel;

type alert_level =
  | [@@@ with_num_tag 1 (1)] AL_warning: alert_level
  | [@@@ with_num_tag 1 (2)] AL_fatal: alert_level


%splice [ps_alert_level] (gen_parser (`alert_level))


/// enum {
///     close_notify(0),
///     unexpected_message(10),
///     bad_record_mac(20),
///     decryption_failed_RESERVED(21),
///     record_overflow(22),
///     decompression_failure_RESERVED(30),
///     handshake_failure(40),
///     no_certificate_RESERVED(41),
///     bad_certificate(42),
///     unsupported_certificate(43),
///     certificate_revoked(44),
///     certificate_expired(45),
///     certificate_unknown(46),
///     illegal_parameter(47),
///     unknown_ca(48),
///     access_denied(49),
///     decode_error(50),
///     decrypt_error(51),
///     export_restriction_RESERVED(60),
///     protocol_version(70),
///     insufficient_security(71),
///     internal_error(80),
///     inappropriate_fallback(86),
///     user_canceled(90),
///     no_renegotiation_RESERVED(100),
///     missing_extension(109),
///     unsupported_extension(110),
///     certificate_unobtainable_RESERVED(111),
///     unrecognized_name(112),
///     bad_certificate_status_response(113),
///     bad_certificate_hash_value_RESERVED(114),
///     unknown_psk_identity(115),
///     certificate_required(116),
///     no_application_protocol(120),
///     (255)
/// } AlertDescription;

type alert_description =
  | [@@@ with_num_tag 1 (0)]   AD_close_notify: alert_description
  | [@@@ with_num_tag 1 (10)]  AD_unexpected_message: alert_description
  | [@@@ with_num_tag 1 (20)]  AD_bad_record_mac: alert_description
  | [@@@ with_num_tag 1 (21)]  AD_decryption_failed_RESERVED: alert_description
  | [@@@ with_num_tag 1 (22)]  AD_record_overflow: alert_description
  | [@@@ with_num_tag 1 (30)]  AD_decompression_failure_RESERVED: alert_description
  | [@@@ with_num_tag 1 (40)]  AD_handshake_failure: alert_description
  | [@@@ with_num_tag 1 (41)]  AD_no_certificate_RESERVED: alert_description
  | [@@@ with_num_tag 1 (42)]  AD_bad_certificate: alert_description
  | [@@@ with_num_tag 1 (43)]  AD_unsupported_certificate: alert_description
  | [@@@ with_num_tag 1 (44)]  AD_certificate_revoked: alert_description
  | [@@@ with_num_tag 1 (45)]  AD_certificate_expired: alert_description
  | [@@@ with_num_tag 1 (46)]  AD_certificate_unknown: alert_description
  | [@@@ with_num_tag 1 (47)]  AD_illegal_parameter: alert_description
  | [@@@ with_num_tag 1 (48)]  AD_unknown_ca: alert_description
  | [@@@ with_num_tag 1 (49)]  AD_access_denied: alert_description
  | [@@@ with_num_tag 1 (50)]  AD_decode_error: alert_description
  | [@@@ with_num_tag 1 (51)]  AD_decrypt_error: alert_description
  | [@@@ with_num_tag 1 (60)]  AD_export_restriction_RESERVED: alert_description
  | [@@@ with_num_tag 1 (70)]  AD_protocol_version: alert_description
  | [@@@ with_num_tag 1 (71)]  AD_insufficient_security: alert_description
  | [@@@ with_num_tag 1 (80)]  AD_internal_error: alert_description
  | [@@@ with_num_tag 1 (86)]  AD_inappropriate_fallback: alert_description
  | [@@@ with_num_tag 1 (90)]  AD_user_canceled: alert_description
  | [@@@ with_num_tag 1 (100)] AD_no_renegotiation_RESERVED: alert_description
  | [@@@ with_num_tag 1 (109)] AD_missing_extension: alert_description
  | [@@@ with_num_tag 1 (110)] AD_unsupported_extension: alert_description
  | [@@@ with_num_tag 1 (111)] AD_certificate_unobtainable_RESERVED: alert_description
  | [@@@ with_num_tag 1 (112)] AD_unrecognized_name: alert_description
  | [@@@ with_num_tag 1 (113)] AD_bad_certificate_status_response: alert_description
  | [@@@ with_num_tag 1 (114)] AD_bad_certificate_hash_value_RESERVED: alert_description
  | [@@@ with_num_tag 1 (115)] AD_unknown_psk_identity: alert_description
  | [@@@ with_num_tag 1 (116)] AD_certificate_required: alert_description
  | [@@@ with_num_tag 1 (120)] AD_no_application_protocol: alert_description


%splice [ps_alert_description] (gen_parser_with_smt (`alert_description))


/// struct {
///     AlertLevel level;
///     AlertDescription description;
/// } Alert;

type alert (bytes:Type0) {|bytes_like bytes|} = {
  level: alert_level;
  description: alert_description;
}


%splice [ps_alert] (gen_parser (`alert))


/// enum {
///     hello_request_RESERVED(0),
///     client_hello(1),
///     server_hello(2),
///     hello_verify_request_RESERVED(3),
///     new_session_ticket(4),
///     end_of_early_data(5),
///     hello_retry_request_RESERVED(6),
///     encrypted_extensions(8),
///     certificate(11),
///     server_key_exchange_RESERVED(12),
///     certificate_request(13),
///     server_hello_done_RESERVED(14),
///     certificate_verify(15),
///     client_key_exchange_RESERVED(16),
///     finished(20),
///     certificate_url_RESERVED(21),
///     certificate_status_RESERVED(22),
///     supplemental_data_RESERVED(23),
///     key_update(24),
///     message_hash(254),
///     (255)
/// } HandshakeType;

type handshake_type =
  | [@@@ with_num_tag 1 (0)]   HT_hello_request_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (1)]   HT_client_hello: handshake_type
  | [@@@ with_num_tag 1 (2)]   HT_server_hello: handshake_type
  | [@@@ with_num_tag 1 (3)]   HT_hello_verify_request_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (4)]   HT_new_session_ticket: handshake_type
  | [@@@ with_num_tag 1 (5)]   HT_end_of_early_data: handshake_type
  | [@@@ with_num_tag 1 (6)]   HT_hello_retry_request_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (8)]   HT_encrypted_extensions: handshake_type
  | [@@@ with_num_tag 1 (11)]  HT_certificate: handshake_type
  | [@@@ with_num_tag 1 (12)]  HT_server_key_exchange_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (13)]  HT_certificate_request: handshake_type
  | [@@@ with_num_tag 1 (14)]  HT_server_hello_done_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (15)]  HT_certificate_verify: handshake_type
  | [@@@ with_num_tag 1 (16)]  HT_client_key_exchange_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (20)]  HT_finished: handshake_type
  | [@@@ with_num_tag 1 (21)]  HT_certificate_url_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (22)]  HT_certificate_status_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (23)]  HT_supplemental_data_RESERVED: handshake_type
  | [@@@ with_num_tag 1 (24)]  HT_key_update: handshake_type
  | [@@@ with_num_tag 1 (254)] HT_message_hash: handshake_type
  | [@@@ open_tag]
    HT_unknown_handshake_type:
    n:nat_lbytes 1{
      not (
        (0 <= n && n <= 6) ||
        n = 8 ||
        (11 <= n && n <= 16) ||
        (20 <= n && n <= 24) ||
        n = 254
      )
    } ->
    handshake_type

%splice [ps_handshake_type] (gen_parser (`handshake_type))


/// uint16 ProtocolVersion;

type protocol_version = nat_lbytes 2

%splice [ps_protocol_version] (gen_parser (`protocol_version))

let is_legacy_version (v:protocol_version) = v = 0x0303
type legacy_protocol_version = refined protocol_version is_legacy_version
val ps_legacy_protocol_version: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes legacy_protocol_version
let ps_legacy_protocol_version #bytes #bl = refine ps_protocol_version is_legacy_version

/// opaque Random[32];

type random (bytes:Type0) {|bytes_like bytes|} = lbytes bytes 32

%splice [ps_random] (gen_parser (`random))

/// uint8 CipherSuite[2];    /* Cryptographic suite selector */

type cipher_suite = nat_lbytes 2

%splice [ps_cipher_suite] (gen_parser (`cipher_suite))

/// enum {
///     server_name(0),                             /* RFC 6066 */
///     max_fragment_length(1),                     /* RFC 6066 */
///     status_request(5),                          /* RFC 6066 */
///     supported_groups(10),                       /* RFC 8422, 7919 */
///     signature_algorithms(13),                   /* RFC 8446 */
///     use_srtp(14),                               /* RFC 5764 */
///     heartbeat(15),                              /* RFC 6520 */
///     application_layer_protocol_negotiation(16), /* RFC 7301 */
///     signed_certificate_timestamp(18),           /* RFC 6962 */
///     client_certificate_type(19),                /* RFC 7250 */
///     server_certificate_type(20),                /* RFC 7250 */
///     padding(21),                                /* RFC 7685 */
///     RESERVED(40),                               /* Used but never
///                                                    assigned */
///     pre_shared_key(41),                         /* RFC 8446 */
///     early_data(42),                             /* RFC 8446 */
///     supported_versions(43),                     /* RFC 8446 */
///     cookie(44),                                 /* RFC 8446 */
///     psk_key_exchange_modes(45),                 /* RFC 8446 */
///     RESERVED(46),                               /* Used but never
///                                                    assigned */
///     certificate_authorities(47),                /* RFC 8446 */
///     oid_filters(48),                            /* RFC 8446 */
///     post_handshake_auth(49),                    /* RFC 8446 */
///     signature_algorithms_cert(50),              /* RFC 8446 */
///     key_share(51),                              /* RFC 8446 */
///     (65535)
/// } ExtensionType;

type extension_type =
  | [@@@ with_num_tag 2 (0)]  ET_server_name: extension_type
  | [@@@ with_num_tag 2 (1)]  ET_max_fragment_length: extension_type
  | [@@@ with_num_tag 2 (5)]  ET_status_request: extension_type
  | [@@@ with_num_tag 2 (10)] ET_supported_groups: extension_type
  | [@@@ with_num_tag 2 (13)] ET_signature_algorithms: extension_type
  | [@@@ with_num_tag 2 (14)] ET_use_srtp: extension_type
  | [@@@ with_num_tag 2 (15)] ET_heartbeat: extension_type
  | [@@@ with_num_tag 2 (16)] ET_application_layer_protocol_negotiation: extension_type
  | [@@@ with_num_tag 2 (18)] ET_signed_certificate_timestamp: extension_type
  | [@@@ with_num_tag 2 (19)] ET_client_certificate_type: extension_type
  | [@@@ with_num_tag 2 (20)] ET_server_certificate_type: extension_type
  | [@@@ with_num_tag 2 (21)] ET_padding: extension_type
  //| [@@@ with_num_tag 2 (40)] ET_RESERVED: extension_type
  | [@@@ with_num_tag 2 (41)] ET_pre_shared_key: extension_type
  | [@@@ with_num_tag 2 (42)] ET_early_data: extension_type
  | [@@@ with_num_tag 2 (43)] ET_supported_versions: extension_type
  | [@@@ with_num_tag 2 (44)] ET_cookie: extension_type
  | [@@@ with_num_tag 2 (45)] ET_psk_key_exchange_modes: extension_type
  //| [@@@ with_num_tag 2 (46)] ET_RESERVED: extension_type
  | [@@@ with_num_tag 2 (47)] ET_certificate_authorities: extension_type
  | [@@@ with_num_tag 2 (48)] ET_oid_filters: extension_type
  | [@@@ with_num_tag 2 (49)] ET_post_handshake_auth: extension_type
  | [@@@ with_num_tag 2 (50)] ET_signature_algorithms_cert: extension_type
  | [@@@ with_num_tag 2 (51)] ET_key_share: extension_type
  | [@@@ open_tag]
    ET_unknown_extension_type:
    n:nat_lbytes 2{
      not (
        n <= 1 ||
        n = 5 ||
        n = 10 ||
        (13 <= n && n <= 16) ||
        (18 <= n && n <= 21) ||
        (41 <= n && n <= 45) ||
        (47 <= n && n <= 51)
      )
    } ->
    extension_type


%splice [ps_extension_type] (gen_parser (`extension_type))
%splice [ps_extension_type_length] (gen_length_lemma (`extension_type))


/// struct {
///     ExtensionType extension_type;
///     opaque extension_data<0..2^16-1>;
/// } Extension;

type extension (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type;
  extension_data: tls_bytes bytes (({min=0; max=(pow2 16)-1}));
}


%splice [ps_extension] (gen_parser (`extension))
%splice [ps_extension_length] (gen_length_lemma (`extension))

/// struct {
///     ProtocolVersion legacy_version = 0x0303;    /* TLS v1.2 */
///     Random random;
///     opaque legacy_session_id<0..32>;
///     CipherSuite cipher_suites<2..2^16-2>;
///     opaque legacy_compression_methods<1..2^8-1>;
///     Extension extensions<8..2^16-1>;
/// } ClientHello;

type client_hello (bytes:Type0) {|bytes_like bytes|} = {
  legacy_version: legacy_protocol_version;
  random: random bytes;
  legacy_session_id: tls_bytes bytes (({min=0; max=32}));
  cipher_suites: tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2});
  legacy_compression_methods: tls_bytes bytes (({min=1; max=(pow2 8)-1}));
  extensions: tls_list bytes (ps_extension) ({min=8; max=(pow2 16)-1});
}

%splice [ps_client_hello] (gen_parser (`client_hello))
%splice [ps_client_hello_length] (gen_length_lemma (`client_hello))

let is_legacy_compression_method (x:nat_lbytes 1) = x = 0
type legacy_compression_method = refined (nat_lbytes 1) is_legacy_compression_method
val ps_legacy_compression_method: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes legacy_compression_method
let ps_legacy_compression_method #bytes #bl = refine (ps_nat_lbytes 1) is_legacy_compression_method

/// struct {
///     ProtocolVersion legacy_version = 0x0303;    /* TLS v1.2 */
///     Random random;
///     opaque legacy_session_id_echo<0..32>;
///     CipherSuite cipher_suite;
///     uint8 legacy_compression_method = 0;
///     Extension extensions<6..2^16-1>;
/// } ServerHello;

type server_hello (bytes:Type0) {|bytes_like bytes|} = {
  legacy_version: legacy_protocol_version;
  random: random bytes;
  legacy_session_id_echo: tls_bytes bytes (({min=0; max=32}));
  cipher_suite: cipher_suite;
  legacy_compression_method: legacy_compression_method;
  extensions: tls_list bytes (ps_extension) ({min=6; max=(pow2 16)-1});
}

%splice [ps_server_hello] (gen_parser (`server_hello))
%splice [ps_server_hello_length] (gen_length_lemma (`server_hello))

/// enum {
///     unallocated_RESERVED(0x0000),
///     /* Elliptic Curve Groups (ECDHE) */
///     obsolete_RESERVED(0x0001..0x0016),
///     secp256r1(0x0017), secp384r1(0x0018), secp521r1(0x0019),
///     obsolete_RESERVED(0x001A..0x001C),
///     x25519(0x001D), x448(0x001E),
///     /* Finite Field Groups (DHE) */
///     ffdhe2048(0x0100), ffdhe3072(0x0101), ffdhe4096(0x0102),
///     ffdhe6144(0x0103), ffdhe8192(0x0104),
///     /* Reserved Code Points */
///     ffdhe_private_use(0x01FC..0x01FF),
///     ecdhe_private_use(0xFE00..0xFEFF),
///     obsolete_RESERVED(0xFF01..0xFF02),
///     (0xFFFF)
/// } NamedGroup;

type named_group =
  | [@@@ with_num_tag 2 (0x0000)] NG_unallocated_RESERVED: named_group
  // omitted: obsolete_RESERVED (0x0001..0x0016)
  | [@@@ with_num_tag 2 (0x0017)] NG_secp256r1: named_group
  | [@@@ with_num_tag 2 (0x0018)] NG_secp384r1: named_group
  | [@@@ with_num_tag 2 (0x0019)] NG_secp521r1: named_group
  // omitted: obsolete_RESERVED (0x001A..0x001C)
  | [@@@ with_num_tag 2 (0x001D)] NG_x25519: named_group
  | [@@@ with_num_tag 2 (0x001E)] NG_x448: named_group
  | [@@@ with_num_tag 2 (0x0100)] NG_ffdhe2048: named_group
  | [@@@ with_num_tag 2 (0x0101)] NG_ffdhe3072: named_group
  | [@@@ with_num_tag 2 (0x0102)] NG_ffdhe4096: named_group
  | [@@@ with_num_tag 2 (0x0103)] NG_ffdhe6144: named_group
  | [@@@ with_num_tag 2 (0x0104)] NG_ffdhe8192: named_group
  // omitted: ffdhe_private_use (0x01FC..0x01FF)
  // omitted: ecdhe_private_use (0xFE00..0xFEFF)
  // omitted: obsolete_RESERVED (0xFF01..0xFF02)
  | [@@@ open_tag]
    NG_unknown_named_group:
    n:nat_lbytes 2{
      not (
        n = 0x0000 ||
        (0x0017 <= n && n <= 0x0019) ||
        n = 0x001D ||
        n = 0x001E ||
        (0x0100 <= n && n <= 0x0104)
      )
    } ->
    named_group


%splice [ps_named_group] (gen_parser (`named_group))
%splice [ps_named_group_length] (gen_length_lemma (`named_group))


/// struct {
///     NamedGroup group;
///     opaque key_exchange<1..2^16-1>;
/// } KeyShareEntry;

type key_share_entry (bytes:Type0) {|bytes_like bytes|} = {
  group: named_group;
  key_exchange: tls_bytes bytes (({min=1; max=(pow2 16)-1}));
}


%splice [ps_key_share_entry] (gen_parser (`key_share_entry))
%splice [ps_key_share_entry_length] (gen_length_lemma (`key_share_entry))


/// struct {
///     KeyShareEntry client_shares<0..2^16-1>;
/// } KeyShareClientHello;

type key_share_client_hello (bytes:Type0) {|bytes_like bytes|} = {
  client_shares: tls_list bytes (ps_key_share_entry) ({min=0; max=(pow2 16)-1});
}


%splice [ps_key_share_client_hello] (gen_parser (`key_share_client_hello))


/// struct {
///     NamedGroup selected_group;
/// } KeyShareHelloRetryRequest;

type key_share_hello_retry_request (bytes:Type0) {|bytes_like bytes|} = {
  selected_group: named_group;
}


%splice [ps_key_share_hello_retry_request] (gen_parser (`key_share_hello_retry_request))


/// struct {
///     KeyShareEntry server_share;
/// } KeyShareServerHello;

type key_share_server_hello (bytes:Type0) {|bytes_like bytes|} = {
  server_share: key_share_entry bytes;
}


%splice [ps_key_share_server_hello] (gen_parser (`key_share_server_hello))


/// enum { psk_ke(0), psk_dhe_ke(1), (255) } PskKeyExchangeMode;

type psk_key_exchange_mode (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 1 (0)] PKEM_psk_ke: psk_key_exchange_mode bytes
  | [@@@ with_num_tag 1 (1)] PKEM_psk_dhe_ke: psk_key_exchange_mode bytes


%splice [ps_psk_key_exchange_mode] (gen_parser (`psk_key_exchange_mode))


/// struct {
///     PskKeyExchangeMode ke_modes<1..255>;
/// } PskKeyExchangeModes;

type psk_key_exchange_modes (bytes:Type0) {|bytes_like bytes|} = {
  ke_modes: tls_list bytes (ps_psk_key_exchange_mode) ({min=1; max=255});
}


%splice [ps_psk_key_exchange_modes] (gen_parser (`psk_key_exchange_modes))


/// struct {} Empty;

[@@ can_be_unit]
type empty = unit

%splice [ps_empty] (gen_parser (`empty))

/// struct {
///     select (Handshake.msg_type) {
///         case new_session_ticket:   uint32 max_early_data_size;
///         case client_hello:         Empty;
///         case encrypted_extensions: Empty;
///     };
/// } EarlyDataIndication;

[@@ can_be_unit]
let early_data_indication (ty:handshake_type) =
  match ty with
  | HT_new_session_ticket -> nat_lbytes 4
  | HT_client_hello -> empty
  | HT_encrypted_extensions -> empty
  | _ -> empty

%splice [ps_early_data_indication] (gen_parser (`early_data_indication))

/// struct {
///     opaque identity<1..2^16-1>;
///     uint32 obfuscated_ticket_age;
/// } PskIdentity;

type psk_identity (bytes:Type0) {|bytes_like bytes|} = {
  identity: tls_bytes bytes (({min=1; max=(pow2 16)-1}));
  obfuscated_ticket_age: nat_lbytes 4;
}


%splice [ps_psk_identity] (gen_parser (`psk_identity))


/// opaque PskBinderEntry<32..255>;

type psk_binder_entry (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=32; max=255})

%splice [ps_psk_binder_entry] (gen_parser (`psk_binder_entry))

/// struct {
///     PskIdentity identities<7..2^16-1>;
///     PskBinderEntry binders<33..2^16-1>;
/// } OfferedPsks;

type offered_psks (bytes:Type0) {|bytes_like bytes|} = {
  identities: tls_list bytes (ps_psk_identity) ({min=7; max=(pow2 16)-1});
  binders: tls_list bytes (ps_psk_binder_entry) ({min=33; max=(pow2 16)-1});
}


%splice [ps_offered_psks] (gen_parser (`offered_psks))


/// struct {
///     select (Handshake.msg_type) {
///         case client_hello: OfferedPsks;
///         case server_hello: uint16 selected_identity;
///     };
/// } PreSharedKeyExtension;

[@@ can_be_unit]
let pre_shared_key_extension (bytes:Type0) {|bytes_like bytes|} (ty:handshake_type) =
  match ty with
  | HT_client_hello -> offered_psks bytes
  | HT_server_hello -> nat_lbytes 2
  | _ -> empty

%splice [ps_pre_shared_key_extension] (gen_parser (`pre_shared_key_extension))

/// struct {
///     select (Handshake.msg_type) {
///         case client_hello:
///              ProtocolVersion versions<2..254>;
///         case server_hello: /* and HelloRetryRequest */
///              ProtocolVersion selected_version;
///     };
/// } SupportedVersions;

[@@ can_be_unit]
let supported_versions (bytes:Type0) {|bytes_like bytes|} (ty:handshake_type) =
  match ty with
  | HT_client_hello -> tls_list bytes ps_protocol_version ({min=2; max=254})
  | HT_server_hello -> protocol_version
  | _ -> empty

%splice [ps_supported_versions] (gen_parser (`supported_versions))

/// struct {
///     opaque cookie<1..2^16-1>;
/// } Cookie;

type cookie (bytes:Type0) {|bytes_like bytes|} = {
  cookie_: tls_bytes bytes (({min=1; max=(pow2 16)-1}));
}


%splice [ps_cookie] (gen_parser (`cookie))


/// enum {
///     /* RSASSA-PKCS1-v1_5 algorithms */
///     rsa_pkcs1_sha256(0x0401),
///     rsa_pkcs1_sha384(0x0501),
///     rsa_pkcs1_sha512(0x0601),
///     /* ECDSA algorithms */
///     ecdsa_secp256r1_sha256(0x0403),
///     ecdsa_secp384r1_sha384(0x0503),
///     ecdsa_secp521r1_sha512(0x0603),
///     /* RSASSA-PSS algorithms with public key OID rsaEncryption */
///     rsa_pss_rsae_sha256(0x0804),
///     rsa_pss_rsae_sha384(0x0805),
///     rsa_pss_rsae_sha512(0x0806),
///     /* EdDSA algorithms */
///     ed25519(0x0807),
///     ed448(0x0808),
///     /* RSASSA-PSS algorithms with public key OID RSASSA-PSS */
///     rsa_pss_pss_sha256(0x0809),
///     rsa_pss_pss_sha384(0x080a),
///     rsa_pss_pss_sha512(0x080b),
///     /* Legacy algorithms */
///     rsa_pkcs1_sha1(0x0201),
///     ecdsa_sha1(0x0203),
///     /* Reserved Code Points */
///     obsolete_RESERVED(0x0000..0x0200),
///     dsa_sha1_RESERVED(0x0202),
///     obsolete_RESERVED(0x0204..0x0400),
///     dsa_sha256_RESERVED(0x0402),
///     obsolete_RESERVED(0x0404..0x0500),
///     dsa_sha384_RESERVED(0x0502),
///     obsolete_RESERVED(0x0504..0x0600),
///     dsa_sha512_RESERVED(0x0602),
///     obsolete_RESERVED(0x0604..0x06FF),
///     private_use(0xFE00..0xFFFF),
///     (0xFFFF)
/// } SignatureScheme;

type signature_scheme =
  | [@@@ with_num_tag 2 (0x0401)] SS_rsa_pkcs1_sha256: signature_scheme
  | [@@@ with_num_tag 2 (0x0501)] SS_rsa_pkcs1_sha384: signature_scheme
  | [@@@ with_num_tag 2 (0x0601)] SS_rsa_pkcs1_sha512: signature_scheme
  | [@@@ with_num_tag 2 (0x0403)] SS_ecdsa_secp256r1_sha256: signature_scheme
  | [@@@ with_num_tag 2 (0x0503)] SS_ecdsa_secp384r1_sha384: signature_scheme
  | [@@@ with_num_tag 2 (0x0603)] SS_ecdsa_secp521r1_sha512: signature_scheme
  | [@@@ with_num_tag 2 (0x0804)] SS_rsa_pss_rsae_sha256: signature_scheme
  | [@@@ with_num_tag 2 (0x0805)] SS_rsa_pss_rsae_sha384: signature_scheme
  | [@@@ with_num_tag 2 (0x0806)] SS_rsa_pss_rsae_sha512: signature_scheme
  | [@@@ with_num_tag 2 (0x0807)] SS_ed25519: signature_scheme
  | [@@@ with_num_tag 2 (0x0808)] SS_ed448: signature_scheme
  | [@@@ with_num_tag 2 (0x0809)] SS_rsa_pss_pss_sha256: signature_scheme
  | [@@@ with_num_tag 2 (0x080a)] SS_rsa_pss_pss_sha384: signature_scheme
  | [@@@ with_num_tag 2 (0x080b)] SS_rsa_pss_pss_sha512: signature_scheme
  | [@@@ with_num_tag 2 (0x0201)] SS_rsa_pkcs1_sha1: signature_scheme
  | [@@@ with_num_tag 2 (0x0203)] SS_ecdsa_sha1: signature_scheme
  // omitted: obsolete_RESERVED (0x0000..0x0200)
  | [@@@ with_num_tag 2 (0x0202)] SS_dsa_sha1_RESERVED: signature_scheme
  // omitted: obsolete_RESERVED (0x0204..0x0400)
  | [@@@ with_num_tag 2 (0x0402)] SS_dsa_sha256_RESERVED: signature_scheme
  // omitted: obsolete_RESERVED (0x0404..0x0500)
  | [@@@ with_num_tag 2 (0x0502)] SS_dsa_sha384_RESERVED: signature_scheme
  // omitted: obsolete_RESERVED (0x0504..0x0600)
  | [@@@ with_num_tag 2 (0x0602)] SS_dsa_sha512_RESERVED: signature_scheme
  // omitted: obsolete_RESERVED (0x0604..0x06FF)
  // omitted: private_use (0xFE00..0xFFFF)
  | [@@@ open_tag]
    SS_unknown_signature_scheme:
    n:nat_lbytes 2{
      not (
        n = 0x0401 ||
        n = 0x0501 ||
        n = 0x0601 ||
        n = 0x0403 ||
        n = 0x0503 ||
        n = 0x0603 ||
        (0x0804 <= n && n <= 0x080b) ||
        n = 0x0201 ||
        n = 0x0203 ||
        n = 0x0202 ||
        n = 0x0402 ||
        n = 0x0502 ||
        n = 0x0602
      )
    } ->
    signature_scheme


%splice [ps_signature_scheme] (gen_parser (`signature_scheme))
%splice [ps_signature_scheme_length] (gen_length_lemma (`signature_scheme))


/// struct {
///     SignatureScheme supported_signature_algorithms<2..2^16-2>;
/// } SignatureSchemeList;

type signature_scheme_list (bytes:Type0) {|bytes_like bytes|} = {
  supported_signature_algorithms: tls_list bytes (ps_signature_scheme) ({min=2; max=(pow2 16)-2});
}


%splice [ps_signature_scheme_list] (gen_parser (`signature_scheme_list))
%splice [ps_signature_scheme_list_length] (gen_length_lemma (`signature_scheme_list))


/// struct {
///     NamedGroup named_group_list<2..2^16-1>;
/// } NamedGroupList;

type named_group_list (bytes:Type0) {|bytes_like bytes|} = {
  named_group_list_: tls_list bytes (ps_named_group) ({min=2; max=(pow2 16)-1});
}


%splice [ps_named_group_list] (gen_parser (`named_group_list))
%splice [ps_named_group_list_length] (gen_length_lemma (`named_group_list))


/// opaque DistinguishedName<1..2^16-1>;

type distinguished_name (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=1; max=((pow2 16)-1)})

%splice [ps_distinguished_name] (gen_parser (`distinguished_name))

/// struct {
///     DistinguishedName authorities<3..2^16-1>;
/// } CertificateAuthoritiesExtension;

type certificate_authorities_extension (bytes:Type0) {|bytes_like bytes|} = {
  authorities: tls_list bytes (ps_distinguished_name) ({min=3; max=(pow2 16)-1});
}


%splice [ps_certificate_authorities_extension] (gen_parser (`certificate_authorities_extension))


/// struct {
///     opaque certificate_extension_oid<1..2^8-1>;
///     opaque certificate_extension_values<0..2^16-1>;
/// } OIDFilter;

type oid_filter (bytes:Type0) {|bytes_like bytes|} = {
  certificate_extension_oid: tls_bytes bytes (({min=1; max=(pow2 8)-1}));
  certificate_extension_values: tls_bytes bytes (({min=0; max=(pow2 16)-1}));
}


%splice [ps_oid_filter] (gen_parser (`oid_filter))


/// struct {
///     OIDFilter filters<0..2^16-1>;
/// } OIDFilterExtension;

type oid_filter_extension (bytes:Type0) {|bytes_like bytes|} = {
  filters: tls_list bytes (ps_oid_filter) ({min=0; max=(pow2 16)-1});
}


%splice [ps_oid_filter_extension] (gen_parser (`oid_filter_extension))


/// struct {} PostHandshakeAuth;

[@@ can_be_unit]
type post_handshake_auth = unit

%splice [ps_post_handshake_auth] (gen_parser (`post_handshake_auth))

/// struct {
///     Extension extensions<0..2^16-1>;
/// } EncryptedExtensions;

type encrypted_extensions (bytes:Type0) {|bytes_like bytes|} = {
  extensions: tls_list bytes (ps_extension) ({min=0; max=(pow2 16)-1});
}


%splice [ps_encrypted_extensions] (gen_parser (`encrypted_extensions))
%splice [ps_encrypted_extensions_length] (gen_length_lemma (`encrypted_extensions))


/// struct {
///     opaque certificate_request_context<0..2^8-1>;
///     Extension extensions<2..2^16-1>;
/// } CertificateRequest;

type certificate_request (bytes:Type0) {|bytes_like bytes|} = {
  certificate_request_context: tls_bytes bytes (({min=0; max=(pow2 8)-1}));
  extensions: tls_list bytes (ps_extension) ({min=2; max=(pow2 16)-1});
}


%splice [ps_certificate_request] (gen_parser (`certificate_request))
%splice [ps_certificate_request_length] (gen_length_lemma (`certificate_request))


/// enum {
///     X509(0),
///     OpenPGP_RESERVED(1),
///     RawPublicKey(2),
///     (255)
/// } CertificateType;

type certificate_type =
  | [@@@ with_num_tag 1 (0)] CT_X509: certificate_type
  | [@@@ with_num_tag 1 (1)] CT_OpenPGP_RESERVED: certificate_type
  | [@@@ with_num_tag 1 (2)] CT_RawPublicKey: certificate_type
  | [@@@ open_tag]
    CT_unknown_certificate_type:
    n:nat_lbytes 1{
      not (
        n <= 2
      )
    } ->
    certificate_type


%splice [ps_certificate_type] (gen_parser (`certificate_type))


/// struct {
///     select (certificate_type) {
///         case RawPublicKey:
///           /* From RFC 7250 ASN.1_subjectPublicKeyInfo */
///           opaque ASN1_subjectPublicKeyInfo<1..2^24-1>;
///         case X509:
///           opaque cert_data<1..2^24-1>;
///     };
///     Extension extensions<0..2^16-1>;
/// } CertificateEntry;

// This type is parametrized by the certificate type.
// However, every branch leads to the same type, so we can factorize things
type certificate_entry (bytes:Type0) {|bytes_like bytes|} = {
  public_key_or_cert_data: tls_bytes bytes ({min=1; max=((pow2 24)-1)});
  extensions: tls_list bytes ps_extension ({min=0; max=((pow2 16)-1)});
}

%splice [ps_certificate_entry] (gen_parser (`certificate_entry))

/// struct {
///     opaque certificate_request_context<0..2^8-1>;
///     CertificateEntry certificate_list<0..2^24-1>;
/// } Certificate;

type certificate (bytes:Type0) {|bytes_like bytes|} = {
  certificate_request_context: tls_bytes bytes (({min=0; max=(pow2 8)-1}));
  certificate_list: tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1});
}


%splice [ps_certificate] (gen_parser (`certificate))


/// struct {
///     SignatureScheme algorithm;
///     opaque signature<0..2^16-1>;
/// } CertificateVerify;

type certificate_verify (bytes:Type0) {|bytes_like bytes|} = {
  algorithm: signature_scheme;
  signature: tls_bytes bytes (({min=0; max=(pow2 16)-1}));
}


%splice [ps_certificate_verify] (gen_parser (`certificate_verify))


/// struct {
///     opaque verify_data[Hash.length];
/// } Finished;

(*
val cipher_suite_to_hash_length: cipher_suite -> nat
let cipher_suite_to_hash_length cs =
  match cs with
  | 0x1301 -> 32 // TLS_AES_128_GCM_SHA256
  | 0x1302 -> 48 // TLS_AES_256_GCM_SHA384
  | 0x1303 -> 32 // TLS_CHACHA20_POLY1305_SHA256
  | 0x1304 -> 32 // TLS_AES_128_CCM_SHA256
  | 0x1305 -> 32 // TLS_AES_128_CCM_8_SHA256
  | _ -> 32
*)

type finished (bytes:Type0) {|bytes_like bytes|} = {
  verify_data: bytes;
}

val ps_whole_finished: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer_whole bytes (finished bytes)
let ps_whole_finished #bytes #bl =
  isomorphism_whole ps_whole_bytes ({
    a_to_b = (fun (x:bytes) -> {verify_data = x;});
    b_to_a = (fun (x:finished bytes) -> x.verify_data);
    a_to_b_to_a = (fun _ -> ());
    b_to_a_to_b = (fun _ -> ());
  })

/// struct {
///     uint32 ticket_lifetime;
///     uint32 ticket_age_add;
///     opaque ticket_nonce<0..255>;
///     opaque ticket<1..2^16-1>;
///     Extension extensions<0..2^16-2>;
/// } NewSessionTicket;

type new_session_ticket (bytes:Type0) {|bytes_like bytes|} = {
  ticket_lifetime: nat_lbytes 4;
  ticket_age_add: nat_lbytes 4;
  ticket_nonce: tls_bytes bytes (({min=0; max=255}));
  ticket: tls_bytes bytes (({min=1; max=(pow2 16)-1}));
  extensions: tls_list bytes (ps_extension) ({min=0; max=(pow2 16)-2});
}


%splice [ps_new_session_ticket] (gen_parser (`new_session_ticket))


/// struct {} EndOfEarlyData;

[@@ can_be_unit]
type end_of_early_data = unit

%splice [ps_end_of_early_data] (gen_parser (`end_of_early_data))

/// enum {
///     update_not_requested(0), update_requested(1), (255)
/// } KeyUpdateRequest;

type key_update_request =
  | [@@@ with_num_tag 1 (0)] KUR_update_not_requested: key_update_request
  | [@@@ with_num_tag 1 (1)] KUR_update_requested: key_update_request


%splice [ps_key_update_request] (gen_parser (`key_update_request))


/// struct {
///     KeyUpdateRequest request_update;
/// } KeyUpdate;

type key_update (bytes:Type0) {|bytes_like bytes|} = {
  request_update: key_update_request;
}


%splice [ps_key_update] (gen_parser (`key_update))




/// struct {
///     HandshakeType msg_type;    /* handshake type */
///     uint24 length;             /* bytes in message */
///     select (Handshake.msg_type) {
///         case client_hello:          ClientHello;
///         case server_hello:          ServerHello;
///         case end_of_early_data:     EndOfEarlyData;
///         case encrypted_extensions:  EncryptedExtensions;
///         case certificate_request:   CertificateRequest;
///         case certificate:           Certificate;
///         case certificate_verify:    CertificateVerify;
///         case finished:              Finished;
///         case new_session_ticket:    NewSessionTicket;
///         case key_update:            KeyUpdate;
///     };
/// } Handshake;

val handshake_message:
  bytes:Type0 -> {|bytes_like bytes|} ->
  handshake_type ->
  Type0
let handshake_message bytes #bl htype =
  match htype with
  | HT_client_hello -> client_hello bytes
  | HT_server_hello -> server_hello bytes
  | HT_end_of_early_data -> end_of_early_data
  | HT_encrypted_extensions -> encrypted_extensions bytes
  | HT_certificate_request -> certificate_request bytes
  | HT_certificate -> certificate bytes
  | HT_certificate_verify -> certificate_verify bytes
  | HT_finished -> finished bytes
  | HT_new_session_ticket -> new_session_ticket bytes
  | HT_key_update -> key_update bytes
  | _ -> bytes

val ps_whole_handshake_message:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  htype:handshake_type ->
  parser_serializer_whole bytes (handshake_message bytes htype)
let ps_whole_handshake_message #bytes #bl htype =
  match htype with
  | HT_client_hello -> ps_prefix_to_ps_whole ps_client_hello
  | HT_server_hello -> ps_prefix_to_ps_whole ps_server_hello
  | HT_end_of_early_data -> ps_prefix_to_ps_whole ps_end_of_early_data
  | HT_encrypted_extensions -> ps_prefix_to_ps_whole ps_encrypted_extensions
  | HT_certificate_request -> ps_prefix_to_ps_whole ps_certificate_request
  | HT_certificate -> ps_prefix_to_ps_whole ps_certificate
  | HT_certificate_verify -> ps_prefix_to_ps_whole ps_certificate_verify
  | HT_finished -> ps_whole_finished
  | HT_new_session_ticket -> ps_prefix_to_ps_whole ps_new_session_ticket
  | HT_key_update -> ps_prefix_to_ps_whole ps_key_update
  | _ -> ps_whole_bytes

type fixed_length_handshake_message (bytes:Type0) {|bytes_like bytes|} (htype:handshake_type) (length:nat) =
  refined (handshake_message bytes htype) (ps_whole_length_pred (ps_whole_handshake_message htype) length)

val ps_fixed_length_handshake_message:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  htype:handshake_type -> length:nat ->
  parser_serializer_prefix bytes (fixed_length_handshake_message bytes htype length)
let ps_fixed_length_handshake_message #bytes #bl htype length =
  ps_whole_to_ps_prefix length (refine_whole (ps_whole_handshake_message htype) (ps_whole_length_pred (ps_whole_handshake_message htype) length))

type handshake (bytes:Type0) {|bytes_like bytes|} = {
  msg_type: handshake_type;
  length: nat_lbytes 3;
  msg: fixed_length_handshake_message bytes msg_type length;
}

%splice [ps_handshake] (gen_parser (`handshake))

/// Many of the cryptographic computations in TLS make use of a
/// transcript hash.  This value is computed by hashing the concatenation
/// of each included handshake message, including the handshake message
/// header carrying the handshake message type and length fields, but not
/// including record layer headers.  I.e.,
///
///  Transcript-Hash(M1, M2, ... Mn) = Hash(M1 || M2 || ... || Mn)

type tls_transcript (bytes:Type0) {|bytes_like bytes|} =
  list (handshake bytes)

val ps_tls_transcript: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer_whole bytes (tls_transcript bytes)
let ps_tls_transcript #bytes #bl =
  ps_whole_list ps_handshake
