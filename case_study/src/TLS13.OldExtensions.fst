module TLS13.OldExtensions

open Comparse
open TLS13.MessageFormats

// RFC6066

/// enum {
///     host_name(0), (255)
/// } NameType;

type name_type =
  | [@@@ with_num_tag 1 (0)] NT_host_name: name_type


%splice [ps_name_type] (gen_parser (`name_type))

/// opaque HostName<1..2^16-1>;

type host_name (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min = 1; max = (pow2 16)-1})

%splice [ps_host_name] (gen_parser (`host_name))

/// struct {
///     NameType name_type;
///     select (name_type) {
///         case host_name: HostName;
///     } name;
/// } ServerName;

type server_name (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag NT_host_name]
    SN_host_name:
    host_name bytes ->
    server_name bytes

%splice [ps_server_name] (gen_parser (`server_name))

/// struct {
///     ServerName server_name_list<1..2^16-1>
/// } ServerNameList;

type server_name_list (bytes:Type0) {|bytes_like bytes|} = {
  server_name_list_: tls_list bytes ps_server_name ({min = 1; max = (pow2 16)-1});
}

%splice [ps_server_name_list] (gen_parser (`server_name_list))

/// enum{
///     2^9(1), 2^10(2), 2^11(3), 2^12(4), (255)
/// } MaxFragmentLength;

type max_fragment_length =
   | [@@@ with_num_tag 1 (1)] MFL_2_pow_9: max_fragment_length
   | [@@@ with_num_tag 1 (2)] MFL_2_pow_10: max_fragment_length
   | [@@@ with_num_tag 1 (3)] MFL_2_pow_11: max_fragment_length
   | [@@@ with_num_tag 1 (4)] MFL_2_pow_12: max_fragment_length

%splice [ps_max_fragment_length] (gen_parser (`max_fragment_length))

/// enum { ocsp(1), (255) } CertificateStatusType;

type certificate_status_type =
  | [@@@ with_num_tag 1 (1)] CST_ocsp: certificate_status_type


%splice [ps_certificate_status_type] (gen_parser (`certificate_status_type))

/// opaque ResponderID<1..2^16-1>;
/// opaque Extensions<0..2^16-1>;
/// struct {
///     ResponderID responder_id_list<0..2^16-1>;
///     Extensions  request_extensions;
/// } OCSPStatusRequest;

type oscpsr_responder_id (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=1; max=(pow2 16)-1})

%splice [ps_oscpsr_responder_id] (gen_parser (`oscpsr_responder_id))

type ocsp_status_request (bytes:Type0) {|bytes_like bytes|} = {
  responder_id_list: tls_seq bytes (ps_oscpsr_responder_id) ({min=0; max=(pow2 16)-1});
  request_extensions: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_ocsp_status_request] (gen_parser (`ocsp_status_request))

/// struct {
///     CertificateStatusType status_type;
///     select (status_type) {
///         case ocsp: OCSPStatusRequest;
///     } request;
/// } CertificateStatusRequest;

type certificate_status_request (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag CST_ocsp]
    CSR_oscp:
    host_name bytes ->
    certificate_status_request bytes

%splice [ps_certificate_status_request] (gen_parser (`certificate_status_request))

// RFC5764

/// uint8 SRTPProtectionProfile[2];

type srtp_protection_profile = nat_lbytes 2

%splice [ps_srtp_protection_profile] (gen_parser (`srtp_protection_profile))



/// SRTPProtectionProfile SRTPProtectionProfiles<2..2^16-1>;
/// struct {
///    SRTPProtectionProfiles SRTPProtectionProfiles;
///    opaque srtp_mki<0..255>;
/// } UseSRTPData;

type use_srtp_data (bytes:Type0) {|bytes_like bytes|} = {
  srtp_protection_profiles: tls_list bytes ps_srtp_protection_profile ({min=2; max=(pow2 16)-1});
  srtp_mki: tls_bytes bytes (({min=0; max=255}));
}


%splice [ps_use_srtp_data] (gen_parser (`use_srtp_data))

// RFC6520

/// enum {
///    peer_allowed_to_send(1),
///    peer_not_allowed_to_send(2),
///    (255)
/// } HeartbeatMode;

type heartbeat_mode (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 1 (1)] HM_peer_allowed_to_send: heartbeat_mode bytes
  | [@@@ with_num_tag 1 (2)] HM_peer_not_allowed_to_send: heartbeat_mode bytes

%splice [ps_heartbeat_mode] (gen_parser (`heartbeat_mode))


/// struct {
///    HeartbeatMode mode;
/// } HeartbeatExtension;

type heartbeat_extension (bytes:Type0) {|bytes_like bytes|} = {
  mode: heartbeat_mode bytes;
}

%splice [ps_heartbeat_extension] (gen_parser (`heartbeat_extension))

// RFC7301

/// opaque ProtocolName<1..2^8-1>;

type protocol_name (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=1; max=(pow2 8)-1})

%splice [ps_protocol_name] (gen_parser (`protocol_name))

/// struct {
///     ProtocolName protocol_name_list<2..2^16-1>
/// } ProtocolNameList;

type protocol_name_list (bytes:Type0) {|bytes_like bytes|} = {
  protocol_name_list_: tls_list bytes ps_protocol_name ({min=2; max=(pow2 16)-1});
}

%splice [ps_protocol_name_list] (gen_parser (`protocol_name_list))

// RFC6962

/// opaque SerializedSCT<1..2^16-1>;

type serialized_sct (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=1; max=(pow2 16)-1})

%splice [ps_serialized_sct] (gen_parser (`serialized_sct))

/// struct {
///     SerializedSCT sct_list <1..2^16-1>;
/// } SignedCertificateTimestampList;

type signed_certificate_timestamp_list (bytes:Type0) {|bytes_like bytes|} = {
  sct_list: tls_seq bytes (ps_serialized_sct) ({min=1; max=(pow2 16)-1});
}

%splice [ps_signed_certificate_timestamp_list] (gen_parser (`signed_certificate_timestamp_list))

// RFC7250

/// struct {
///         select(ClientOrServerExtension) {
///             case client:
///               CertificateType client_certificate_types<1..2^8-1>;
///             case server:
///               CertificateType client_certificate_type;
///         }
/// } ClientCertTypeExtension;

type client_or_server_extension =
  | COSE_client: client_or_server_extension
  | COSE_server: client_or_server_extension

let client_cert_type_extension (bytes:Type0) {|bytes_like bytes|} (ext_orig:client_or_server_extension) =
  match ext_orig with
  | COSE_client -> tls_list bytes ps_certificate_type ({min=1; max=(pow2 8)-1})
  | COSE_server -> certificate_type

%splice [ps_client_cert_type_extension] (gen_parser (`client_cert_type_extension))


/// struct {
///         select(ClientOrServerExtension) {
///             case client:
///               CertificateType server_certificate_types<1..2^8-1>;
///             case server:
///               CertificateType server_certificate_type;
///         }
/// } ServerCertTypeExtension;


let server_cert_type_extension (bytes:Type0) {|bytes_like bytes|} (ext_orig:client_or_server_extension) =
  match ext_orig with
  | COSE_client -> tls_list bytes ps_certificate_type ({min=1; max=(pow2 8)-1})
  | COSE_server -> certificate_type

%splice [ps_server_cert_type_extension] (gen_parser (`server_cert_type_extension))
