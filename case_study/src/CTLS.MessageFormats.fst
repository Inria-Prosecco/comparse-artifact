module CTLS.MessageFormats

open FStar.List.Tot
open Comparse
open TLS13.MessageFormats
open TLS13.OldExtensions
open CTLS.Profile

#set-options "--fuel 0 --ifuel 0"

noeq
type ctls_unknowns (bytes:Type0) {|bytes_like bytes|} = {
  ctls_template_handshake_type: ht:handshake_type{HT_unknown_handshake_type? ht};
  self_delimiting_extension: etype:extension_type{ET_unknown_extension_type? etype} -> option (typ:Type0 & parser_serializer_prefix bytes typ);
  is_x509_certificate: bytes -> bool;
}

val no_template_dep: #bytes:Type0 -> {|bytes_like bytes|} -> a:Type0 -> (ctls_template bytes -> Type0)
let no_template_dep #bytes a t = a

val mk_templated_type:
  #a:Type0 -> bytes:Type0 -> {|bytes_like bytes|} ->
  (ctls_template bytes -> option a) ->
  Type0 -> (a -> Type0) ->
  (ctls_template bytes -> Type0)
let mk_templated_type #a bytes #bl get_template_elem default_ty parametric_ty template =
  match get_template_elem template with
  | None -> default_ty
  | Some param -> parametric_ty param

val ps_mk_templated_type:
  #a:Type0 ->
  #default_ty:Type0 -> #parametric_ty:(a -> Type0) ->
  bytes:Type0 -> {|bytes_like bytes|} ->
  get_template_elem:(ctls_template bytes -> option a) ->
  parser_serializer_prefix bytes default_ty ->
  (param:a -> parser_serializer_prefix bytes (parametric_ty param)) ->
  (template:ctls_template bytes -> parser_serializer_prefix bytes (mk_templated_type bytes get_template_elem default_ty parametric_ty template))
let ps_mk_templated_type #a #default_ty #parametric_ty bytes #bl get_template_elem ps_default_ty ps_parametric_ty template =
  match get_template_elem template with
  | None -> ps_default_ty
  | Some param -> ps_parametric_ty param

(*** Ciphersuite ***)

val get_cipher_suite_template: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_template bytes -> option (ctls_cipher_suite_template bytes)
let get_cipher_suite_template #bytes #bl t =
  get_template_element ps_ctls_cipher_suite_template CTLSTET_cipher_suite t

[@@ can_be_unit]
type pre_ctls_cipher_suites (bytes:Type0) {|bytes_like bytes|} (cipher_suite:ctls_cipher_suite_template bytes) =
  unit

%splice [ps_pre_ctls_cipher_suites] (gen_parser (`pre_ctls_cipher_suites))

type ctls_cipher_suites (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_cipher_suite_template (tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2})) (pre_ctls_cipher_suites bytes)

let ps_ctls_cipher_suites (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_cipher_suite_template (ps_tls_list (ps_cipher_suite) ({min=2; max=(pow2 16)-2})) ps_pre_ctls_cipher_suites

[@@ can_be_unit]
type pre_ctls_cipher_suite (bytes:Type0) {|bytes_like bytes|} (cipher_suite:ctls_cipher_suite_template bytes) =
  unit

%splice [ps_pre_ctls_cipher_suite] (gen_parser (`pre_ctls_cipher_suite))

type ctls_cipher_suite (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_cipher_suite_template cipher_suite (pre_ctls_cipher_suite bytes)

let ps_ctls_cipher_suite (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_cipher_suite_template ps_cipher_suite ps_pre_ctls_cipher_suite


(*** DH group ***)

val get_dh_group_template: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_template bytes -> option (ctls_dh_group_template bytes)
let get_dh_group_template #bytes #bl t =
  get_template_element ps_ctls_dh_group_template CTLSTET_dh_group t

type pre_ctls_key_share_entry (bytes:Type0) {|bytes_like bytes|} (dh_group:ctls_dh_group_template bytes) = (
  if dh_group.key_share_length = 0 then
    // opaque key_exchange<1..2^16-1>;
    tls_bytes bytes (({min=1; max=(pow2 16)-1}))
  else
    lbytes bytes dh_group.key_share_length
)

%splice [ps_pre_ctls_key_share_entry] (gen_parser (`pre_ctls_key_share_entry))

type pre_ctls_key_share_client_hello (bytes:Type0) {|bytes_like bytes|} (dh_group:ctls_dh_group_template bytes) = {
  client_shares: pre_ctls_key_share_entry bytes dh_group;
}

%splice [ps_pre_ctls_key_share_client_hello] (gen_parser (`pre_ctls_key_share_client_hello))

type ctls_key_share_client_hello (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_dh_group_template (key_share_client_hello bytes) (pre_ctls_key_share_client_hello bytes)

let ps_ctls_key_share_client_hello (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_dh_group_template ps_key_share_client_hello ps_pre_ctls_key_share_client_hello

type pre_ctls_key_share_server_hello (bytes:Type0) {|bytes_like bytes|} (dh_group:ctls_dh_group_template bytes) = {
  server_share: pre_ctls_key_share_entry bytes dh_group;
}

%splice [ps_pre_ctls_key_share_server_hello] (gen_parser (`pre_ctls_key_share_server_hello))

type ctls_key_share_server_hello (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_dh_group_template (key_share_server_hello bytes) (pre_ctls_key_share_server_hello bytes)

let ps_ctls_key_share_server_hello (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_dh_group_template ps_key_share_server_hello ps_pre_ctls_key_share_server_hello

(*** Signature algorithm ***)

val get_signature_algorithm_template: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_template bytes -> option (ctls_signature_algorithm_template bytes)
let get_signature_algorithm_template #bytes #bl t =
  get_template_element ps_ctls_signature_algorithm_template CTLSTET_signature_algorithm t

// Compression of CertificateVerify.algorithm

[@@ can_be_unit]
type pre_ctls_certificate_verify_algorithm (bytes:Type0) {|bytes_like bytes|} (signature_algorithm:ctls_signature_algorithm_template bytes) =
  unit

%splice [ps_pre_ctls_certificate_verify_algorithm] (gen_parser (`pre_ctls_certificate_verify_algorithm))

type ctls_certificate_verify_algorithm (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_signature_algorithm_template (signature_scheme) (pre_ctls_certificate_verify_algorithm bytes)

let ps_ctls_certificate_verify_algorithm (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_signature_algorithm_template ps_signature_scheme ps_pre_ctls_certificate_verify_algorithm

// Compression of CertificateVerify.signature

type pre_ctls_certificate_verify_signature (bytes:Type0) {|bytes_like bytes|} (signature_algorithm:ctls_signature_algorithm_template bytes) = (
  if signature_algorithm.signature_length = 0 then
    // opaque signature<0..2^16-1>;
    tls_bytes bytes (({min=0; max=(pow2 16)-1}))
  else
    lbytes bytes signature_algorithm.signature_length
)

%splice [ps_pre_ctls_certificate_verify_signature] (gen_parser (`pre_ctls_certificate_verify_signature))

type ctls_certificate_verify_signature (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_signature_algorithm_template (tls_bytes bytes (({min=0; max=(pow2 16)-1}))) (pre_ctls_certificate_verify_signature bytes)

let ps_ctls_certificate_verify_signature (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_signature_algorithm_template (ps_tls_bytes (({min=0; max=(pow2 16)-1}))) ps_pre_ctls_certificate_verify_signature

(*** Random ***)

val get_random_template: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_template bytes -> option (ctls_random_template bytes)
let get_random_template #bytes #bl t =
  get_template_element ps_ctls_random_template CTLSTET_random t

[@@ can_be_unit]
type pre_ctls_random (bytes:Type0) {|bytes_like bytes|} (rand_sz:ctls_random_template bytes) =
  lbytes bytes rand_sz

%splice [ps_pre_ctls_random] (gen_parser (`pre_ctls_random))

type ctls_random (bytes:Type0) {|bytes_like bytes|} =
  mk_templated_type bytes get_random_template (random bytes) (pre_ctls_random bytes)

let ps_ctls_random (bytes:Type0) {|bytes_like bytes|} =
  ps_mk_templated_type bytes get_random_template ps_random ps_pre_ctls_random

(*** Extension ***)

type tls_extension_inner (bytes:Type0) {|bytes_like bytes|} = {
  extension_data: tls_bytes bytes (({min=0; max=(pow2 16)-1}));
}

%splice [ps_tls_extension_inner] (gen_parser (`tls_extension_inner))

noeq
type one_extension_type (bytes:Type0) {|bytes_like bytes|} = {
  typ: ctls_template bytes -> Type0;
  parser: t:ctls_template bytes -> parser_serializer_prefix bytes (typ t);
}

noeq
type ctls_extensions_types (bytes:Type0) {|bytes_like bytes|} = {
  expected_ty: extension_type -> one_extension_type bytes;
  additional_ty: extension_type -> one_extension_type bytes;
}

#push-options "--ifuel 1"
val ctls_expected_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_extensions_types bytes -> ctls_template bytes -> list extension_type -> Type0
let rec ctls_expected_extensions #bytes #bl comp temp ty_list =
  match ty_list with
  | [] -> unit
  | h_ty::t_ty -> (comp.expected_ty h_ty).typ temp & (ctls_expected_extensions comp temp t_ty)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val ps_ctls_expected_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> comp:ctls_extensions_types bytes -> temp:ctls_template bytes -> ty_list:list extension_type -> parser_serializer_prefix bytes (ctls_expected_extensions comp temp ty_list)
let rec ps_ctls_expected_extensions #bytes #bl comp temp ty_list =
  match ty_list with
  | [] ->
    mk_isomorphism
      (ctls_expected_extensions comp temp ty_list)
      ps_unit
      (fun x -> x <: (ctls_expected_extensions comp temp []))
      (fun (x:(ctls_expected_extensions comp temp [])) -> x)
  | h_ty::t_ty -> (
    let f ((|x,y|): (_:((comp.expected_ty h_ty).typ temp) & (ctls_expected_extensions comp temp t_ty))): ctls_expected_extensions comp temp (h_ty::t_ty) =
      (x, y)
    in
    let g ((x,y): ctls_expected_extensions comp temp (h_ty::t_ty)): _:((comp.expected_ty h_ty).typ temp) & (ctls_expected_extensions comp temp t_ty) =
      (|x, y|)
    in
    assert(forall x. f (g x) == x) by (
      let open FStar.Tactics in
      destruct (forall_intro ());
      let _ = intro() in
      let _ = intro() in
      l_to_r [binder_to_term (intro ())];
      trefl()
    );
    mk_isomorphism
      (ctls_expected_extensions comp temp ty_list)
      (bind ((comp.expected_ty h_ty).parser temp) (fun _ -> ps_ctls_expected_extensions comp temp t_ty))
      f
      g
  )
#pop-options

noeq
type compressed_extension (bytes:Type0) {|bytes_like bytes|} (comp:ctls_extensions_types bytes) (temp:ctls_template bytes) = {
  extension_type: extension_type;
  [@@@ with_parser ((comp.additional_ty extension_type).parser temp)]
  extension_data: (comp.additional_ty extension_type).typ temp;
}

%splice [ps_compressed_extension] (gen_parser (`compressed_extension))

noeq
type ctls_extensions_allow_additional_internal (bytes:Type0) {|bytes_like bytes|} (comp:ctls_extensions_types bytes) (expected_exts:list extension_type) (temp:ctls_template bytes) = {
  expected_extensions: ctls_expected_extensions comp temp expected_exts;
  additional_extensions: list (compressed_extension bytes comp temp);
}

val ps_whole_ctls_extensions_allow_additional_internal:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  comp:ctls_extensions_types bytes -> expected_exts:list extension_type -> temp:ctls_template bytes ->
  parser_serializer_whole bytes (ctls_extensions_allow_additional_internal bytes comp expected_exts temp)
let ps_whole_ctls_extensions_allow_additional_internal #bytes #bl comp expected_exts temp =
  mk_isomorphism_whole
    (ctls_extensions_allow_additional_internal bytes comp expected_exts temp)
    (bind_whole (ps_ctls_expected_extensions comp temp expected_exts) (fun _ -> ps_whole_list (ps_compressed_extension comp temp)))
    (fun (|expected_extensions, additional_extensions|) -> {expected_extensions; additional_extensions})
    (fun {expected_extensions; additional_extensions} -> (|expected_extensions, additional_extensions|))


type fixed_length_ctls_extensions_allow_additional_internal (bytes:Type0) {|bytes_like bytes|} (comp:ctls_extensions_types bytes) (expected_exts:list extension_type) (temp:ctls_template bytes) (length:nat) =
  refined (ctls_extensions_allow_additional_internal bytes comp expected_exts temp) (ps_whole_length_pred (ps_whole_ctls_extensions_allow_additional_internal comp expected_exts temp) length)

val ps_fixed_length_ctls_extensions_allow_additional_internal:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  comp:ctls_extensions_types bytes -> expected_exts:list extension_type -> temp:ctls_template bytes -> length:nat ->
  parser_serializer_prefix bytes (fixed_length_ctls_extensions_allow_additional_internal bytes comp expected_exts temp length)
let ps_fixed_length_ctls_extensions_allow_additional_internal #bytes #bl comp expected_exts temp length =
  ps_whole_to_ps_prefix length (refine_whole (ps_whole_ctls_extensions_allow_additional_internal comp expected_exts temp) (ps_whole_length_pred (ps_whole_ctls_extensions_allow_additional_internal comp expected_exts temp) length))

noeq
type ctls_extensions_allow_additional (bytes:Type0) {|bytes_like bytes|} (comp:ctls_extensions_types bytes) (expected_exts:list extension_type) (temp:ctls_template bytes) = {
  length: nat_lbytes 2;
  content: fixed_length_ctls_extensions_allow_additional_internal bytes comp expected_exts temp length;
}

%splice [ps_ctls_extensions_allow_additional] (gen_parser(`ctls_extensions_allow_additional))

type ctls_extensions_template (bytes:Type0) {|bytes_like bytes|} = {
  predefined_extensions: list (extension bytes);
  expected_extensions: list extension_type;
  allow_additional: bool;
}

[@@ can_be_unit]
val extensions_ctls_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_extensions_types bytes -> (ctls_template bytes -> ctls_extensions_template bytes) ->
  ctls_template bytes -> Type0
let extensions_ctls_type #bytes #bl ext_comp get_ext_temp temp =
  let ext_temp = get_ext_temp temp in
  if ext_temp.allow_additional then
    ctls_extensions_allow_additional bytes ext_comp ext_temp.expected_extensions temp
  else (
    ctls_expected_extensions ext_comp temp ext_temp.expected_extensions
  )

%splice [ps_extensions_ctls_type] (gen_parser (`extensions_ctls_type))

type extension_origin =
  | ClientHello: extension_origin
  | ServerHello: extension_origin
  | EncryptedExtensions: extension_origin
  | Certificate: extension_origin
  | CertificateRequest: extension_origin
  | NewSessionTicket: extension_origin
  | HelloRetryRequest: extension_origin

val default_ext_temp:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_extensions_template bytes
let default_ext_temp #bytes #bl = {
  predefined_extensions = [];
  expected_extensions = [];
  allow_additional = true;
}

val get_ctls_extension_template:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_origin -> ctls_template bytes ->
  option (ctls_extension_template bytes)
let get_ctls_extension_template #bytes #bl origin temp =
  match origin with
  | ClientHello ->
    get_template_element ps_ctls_extension_template CTLSTET_client_hello_extensions temp
  | ServerHello ->
    get_template_element ps_ctls_extension_template CTLSTET_server_hello_extensions temp
  | EncryptedExtensions ->
    get_template_element ps_ctls_extension_template CTLSTET_encrypted_extensions temp
  | CertificateRequest ->
    get_template_element ps_ctls_extension_template CTLSTET_certificate_request_extensions temp
  | _ -> None

val convert_ctls_extension_template:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_extension_template bytes ->
  ctls_extensions_template bytes
let convert_ctls_extension_template #bytes #bl t = {
    predefined_extensions = t.predefined_extensions;
    expected_extensions = t.expected_extensions;
    allow_additional = t.allow_additional <> 0;
  }

#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
val compute_ext_temp:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_origin -> ctls_template bytes ->
  ctls_extensions_template bytes
let compute_ext_temp #bytes #bl origin temp =
  let ext_temp =
    match get_ctls_extension_template origin temp with
    | None -> default_ext_temp
    | Some x -> convert_ctls_extension_template x
  in
  let ext_temp =
    match origin, get_dh_group_template temp with
    | ClientHello, Some dh_group
    | EncryptedExtensions, Some dh_group -> (
      let supported_groups_ext: extension bytes = {
        extension_type = ET_supported_groups;
        extension_data = (ps_prefix_to_ps_whole #bytes ps_named_group_list).serialize ({
          named_group_list_ = [dh_group.group_name];
        })
      } in
      { ext_temp with
        predefined_extensions = supported_groups_ext::ext_temp.predefined_extensions;
      }
    )
    | _ -> ext_temp
  in
  let ext_temp =
    match origin, get_signature_algorithm_template temp with
    | ClientHello, Some signature_algorithm
    | CertificateRequest, Some signature_algorithm -> (
      let supported_groups_ext: extension bytes = {
        extension_type = ET_signature_algorithms;
        extension_data = (ps_prefix_to_ps_whole #bytes ps_signature_scheme_list).serialize ({
          supported_signature_algorithms = [signature_algorithm.signature_scheme];
        })
      } in
      { ext_temp with
        predefined_extensions = supported_groups_ext::ext_temp.predefined_extensions;
      }
    )
    | _ -> ext_temp
  in
  ext_temp
#pop-options

#push-options "--ifuel 1"
val extension_origin_to_handshake_type: extension_origin -> handshake_type
let extension_origin_to_handshake_type ext_orig =
  match ext_orig with
  | ClientHello -> HT_client_hello
  | ServerHello -> HT_server_hello
  | EncryptedExtensions -> HT_encrypted_extensions
  | Certificate -> HT_certificate
  | CertificateRequest -> HT_certificate_request
  | NewSessionTicket -> HT_new_session_ticket
  | HelloRetryRequest -> HT_server_hello // See RFC 8446, Section 4.1.3 and 4.1.4
#pop-options

val get_rfc8446_self_delimiting_extension_parser:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_origin -> extension_type ->
  option (a:Type0 & parser_serializer_prefix bytes a)
let get_rfc8446_self_delimiting_extension_parser #bytes #bl ext_orig ext_ty =
  let hs_ty = extension_origin_to_handshake_type ext_orig in
  match ext_ty with
  | ET_server_name ->
    Some (|server_name bytes, ps_server_name|)
  | ET_max_fragment_length ->
    Some (|max_fragment_length, ps_max_fragment_length|)
  | ET_status_request ->
    Some (|ocsp_status_request bytes, ps_ocsp_status_request|)
  | ET_supported_groups ->
    Some (|named_group_list bytes, ps_named_group_list|)
  | ET_signature_algorithms ->
    Some (|signature_scheme_list bytes, ps_signature_scheme_list|)
  | ET_use_srtp ->
    Some (|use_srtp_data bytes, ps_use_srtp_data|)
  | ET_heartbeat ->
    Some (|heartbeat_extension bytes, ps_heartbeat_extension|)
  | ET_application_layer_protocol_negotiation ->
    Some (|protocol_name_list bytes, ps_protocol_name_list|)
  | ET_signed_certificate_timestamp -> (
    match ext_orig with
    | Certificate ->
      Some (|signed_certificate_timestamp_list bytes, ps_signed_certificate_timestamp_list|)
    | ClientHello ->
      Some (|empty, ps_empty|)
    | _ ->
      None
  )
  | ET_client_certificate_type -> (
    match ext_orig with
    | ClientHello ->
      Some (|client_cert_type_extension bytes COSE_client, (ps_client_cert_type_extension COSE_client)|)
    | EncryptedExtensions ->
      Some (|client_cert_type_extension bytes COSE_server, (ps_client_cert_type_extension COSE_server)|)
    | _ -> None
  )
  | ET_server_certificate_type -> (
    match ext_orig with
    | ClientHello ->
      Some (|server_cert_type_extension bytes COSE_client, (ps_server_cert_type_extension COSE_client)|)
    | EncryptedExtensions ->
      Some (|server_cert_type_extension bytes COSE_server, (ps_server_cert_type_extension COSE_server)|)
    | _ -> None
  )
  | ET_pre_shared_key ->
    Some (|pre_shared_key_extension bytes hs_ty, (ps_pre_shared_key_extension hs_ty)|)
  | ET_early_data ->
    Some (|early_data_indication hs_ty, (ps_early_data_indication hs_ty)|)
  | ET_supported_versions ->
    Some (|supported_versions bytes hs_ty, (ps_supported_versions hs_ty)|)
  | ET_cookie ->
    Some (|cookie bytes, ps_cookie|)
  | ET_psk_key_exchange_modes ->
    Some (|psk_key_exchange_mode bytes, ps_psk_key_exchange_mode|)
  | ET_certificate_authorities ->
    Some (|certificate_authorities_extension bytes, ps_certificate_authorities_extension|)
  | ET_oid_filters ->
    Some (|oid_filter_extension bytes, ps_oid_filter_extension|)
  | ET_post_handshake_auth ->
    Some (|post_handshake_auth, ps_post_handshake_auth|)
  | ET_signature_algorithms_cert ->
    Some (|signature_scheme_list bytes, ps_signature_scheme_list|)
  | ET_key_share -> (
    match ext_orig with
    | ClientHello ->
      Some (|key_share_client_hello bytes, ps_key_share_client_hello|)
    | HelloRetryRequest ->
      Some (|key_share_hello_retry_request bytes, ps_key_share_hello_retry_request|)
    | ServerHello ->
      Some (|key_share_server_hello bytes, ps_key_share_server_hello|)
    | _ ->
      None
  )
  | _ -> None

val one_extension_type_for_self_delimiting_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #tls_type:Type0 ->
  parser_serializer_prefix bytes tls_type ->
  one_extension_type bytes
let one_extension_type_for_self_delimiting_extension #bytes #bl #tls_type ps_tls_type = {
  typ = (fun _ -> tls_type);
  parser = (fun _ -> ps_tls_type);
}

val default_one_ext_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  one_extension_type bytes
let default_one_ext_type #bytes #bl =
  {
    typ = (fun _ -> tls_extension_inner bytes);
    parser = (fun _ -> ps_tls_extension_inner);
  }

val compute_ext_type_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_unknowns bytes ->
  extension_origin -> extension_type ->
  one_extension_type bytes
let compute_ext_type_aux #bytes #bl unk origin ext_ty =
  match origin, ext_ty with
  | ClientHello, ET_key_share -> {
    typ = ctls_key_share_client_hello bytes;
    parser = ps_ctls_key_share_client_hello bytes;
  }
  | ServerHello, ET_key_share -> {
    typ = ctls_key_share_server_hello bytes;
    parser = ps_ctls_key_share_server_hello bytes;
  }
  | _, _ -> (
    match get_rfc8446_self_delimiting_extension_parser origin ext_ty with
    | Some (|tls_type, ps_tls_type|) ->
      one_extension_type_for_self_delimiting_extension ps_tls_type
    | None -> (
      match ext_ty with
      | ET_unknown_extension_type _ -> (
        match unk.self_delimiting_extension ext_ty with
        | Some (|ty, ps_ty|) -> {typ = no_template_dep ty; parser = (fun _ -> ps_ty);}
        | None -> default_one_ext_type
      )
      | _ -> default_one_ext_type
    )
  )

val compute_ext_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_unknowns bytes ->
  extension_origin ->
  ctls_extensions_types bytes
let compute_ext_type #bytes #bl unk origin =
  {
    expected_ty = compute_ext_type_aux unk origin;
    additional_ty = compute_ext_type_aux unk origin;
  }

[@@ can_be_unit]
type ctls_extensions (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (ext_orig:extension_origin) (t:ctls_template bytes) =
  extensions_ctls_type (compute_ext_type unk ext_orig) (compute_ext_temp ext_orig) t

%splice [ps_ctls_extensions] (gen_parser (`ctls_extensions))

(*** Handshake messages ***)

/// struct {
///     Random random;
///     CipherSuite cipher_suites<1..2^16-1>;
///     Extension extensions<1..2^16-1>;
/// } ClientHello;

[@@ can_be_unit]
noeq
type ctls_client_hello (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  random: ctls_random bytes t;
  cipher_suites: ctls_cipher_suites bytes t;
  extensions: ctls_extensions bytes unk ClientHello t;
}

%splice [ps_ctls_client_hello] (gen_parser (`ctls_client_hello))

/// struct {
///     Random random;
///     CipherSuite cipher_suite;
///     Extension extensions<1..2^16-1>;
/// } ServerHello;

[@@ can_be_unit]
noeq
type ctls_server_hello (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  random: ctls_random bytes t;
  cipher_suite: ctls_cipher_suite bytes t;
  extensions: ctls_extensions bytes unk ServerHello t;
}

%splice [ps_ctls_server_hello] (gen_parser (`ctls_server_hello))

/// struct {
///     CipherSuite cipher_suite;
///     Extension extensions<2..2^16-1>;
/// } HelloRetryRequest;

[@@ can_be_unit]
noeq
type ctls_hello_retry_request (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  cipher_suite: ctls_cipher_suite bytes t;
  extensions: ctls_extensions bytes unk HelloRetryRequest t;
}

%splice [ps_ctls_hello_retry_request] (gen_parser (`ctls_hello_retry_request))

/// Compression of:
///
/// struct {
///     SignatureScheme algorithm;
///     opaque signature<0..2^16-1>;
/// } CertificateVerify;

[@@ can_be_unit]
noeq
type ctls_certificate_verify (bytes:Type0) {|bytes_like bytes|} (t:ctls_template bytes) = {
  algorithm: ctls_certificate_verify_algorithm bytes t;
  signature: ctls_certificate_verify_signature bytes t;
}

%splice [ps_ctls_certificate_verify] (gen_parser (`ctls_certificate_verify))

/// struct {
///     Extension extensions<0..2^16-1>;
/// } EncryptedExtensions;

[@@ can_be_unit]
noeq
type ctls_encrypted_extensions (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  extensions: ctls_extensions bytes unk EncryptedExtensions t;
}

%splice [ps_ctls_encrypted_extensions] (gen_parser (`ctls_encrypted_extensions))

/// struct {
///     opaque certificate_request_context<0..2^8-1>;
///     Extension extensions<2..2^16-1>;
/// } CertificateRequest;

noeq
type ctls_certificate_request (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  certificate_request_context: tls_bytes bytes (({min=0; max=(pow2 8)-1}));
  extensions: ctls_extensions bytes unk CertificateRequest t;
}

%splice [ps_ctls_certificate_request] (gen_parser (`ctls_certificate_request))

/// When computing the handshake transcript,
/// all handshake messages are represented in TLS Handshake messages,
/// as in DTLS 1.3 ([RFC9147], Section 5.2), regardless of template.handshake_framing.

/// Custom message format to represent a Handshake inside a cTLS transcript
///
/// struct {
///     HandshakeType msg_type;    /* handshake type */
///     uint24 length;             /* bytes in message */
///     select (CTLSTranscriptHandshake.msg_type) {
///         case client_hello:          ClientHello;
///         case server_hello:          ServerHello;
///         case hello_retry_request:   HelloRetryRequest;  /* New */
///         case end_of_early_data:     EndOfEarlyData;
///         case encrypted_extensions:  EncryptedExtensions;
///         case certificate_request:   CertificateRequest;
///         case certificate:           Certificate;
///         case certificate_verify:    CertificateVerify;
///         case finished:              Finished;
///         case new_session_ticket:    NewSessionTicket;
///         case key_update:            KeyUpdate;
///         case request_connection_id: RequestConnectionId;
///         case new_connection_id:     NewConnectionId;
///     };
/// } CTLSTranscriptHandshake;

val ctls_transcript_handshake_message:
  bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_unknowns bytes ->
  ctls_template bytes -> handshake_type ->
  Type0
let ctls_transcript_handshake_message bytes #bl unk t htype =
  match htype with
  | HT_client_hello -> ctls_client_hello bytes unk t
  | HT_server_hello -> ctls_server_hello bytes unk t
  | HT_hello_retry_request_RESERVED -> ctls_hello_retry_request bytes unk t
  | HT_end_of_early_data -> end_of_early_data
  | HT_encrypted_extensions -> ctls_encrypted_extensions bytes unk t
  | HT_certificate_request -> ctls_certificate_request bytes unk t
  | HT_certificate -> certificate bytes
  | HT_certificate_verify -> ctls_certificate_verify bytes t
  | HT_finished -> finished bytes
  | HT_new_session_ticket -> new_session_ticket bytes
  | HT_key_update -> key_update bytes
  | _ -> bytes

val ps_whole_ctls_transcript_handshake_message:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  t:ctls_template bytes -> htype:handshake_type ->
  parser_serializer_whole bytes (ctls_transcript_handshake_message bytes unk t htype)
let ps_whole_ctls_transcript_handshake_message #bytes #bl unk t htype =
  match htype with
  | HT_client_hello -> ps_prefix_to_ps_whole (ps_ctls_client_hello unk t)
  | HT_server_hello -> ps_prefix_to_ps_whole (ps_ctls_server_hello unk t)
  | HT_hello_retry_request_RESERVED -> ps_prefix_to_ps_whole (ps_ctls_hello_retry_request unk t)
  | HT_end_of_early_data -> ps_prefix_to_ps_whole ps_end_of_early_data
  | HT_encrypted_extensions -> ps_prefix_to_ps_whole (ps_ctls_encrypted_extensions unk t)
  | HT_certificate_request -> ps_prefix_to_ps_whole (ps_ctls_certificate_request unk t)
  | HT_certificate -> ps_prefix_to_ps_whole ps_certificate
  | HT_certificate_verify -> ps_prefix_to_ps_whole (ps_ctls_certificate_verify t)
  | HT_finished -> ps_whole_finished
  | HT_new_session_ticket -> ps_prefix_to_ps_whole ps_new_session_ticket
  | HT_key_update -> ps_prefix_to_ps_whole ps_key_update
  | _ -> ps_whole_bytes

type fixed_length_ctls_transcript_handshake_message (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) (htype:handshake_type) (length:nat) =
  refined (ctls_transcript_handshake_message bytes unk t htype) (ps_whole_length_pred (ps_whole_ctls_transcript_handshake_message unk t htype) length)

val ps_fixed_length_ctls_transcript_handshake_message:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  t:ctls_template bytes -> htype:handshake_type -> length:nat ->
  parser_serializer_prefix bytes (fixed_length_ctls_transcript_handshake_message bytes unk t htype length)
let ps_fixed_length_ctls_transcript_handshake_message #bytes #bl unk t htype length =
  ps_whole_to_ps_prefix length (refine_whole (ps_whole_ctls_transcript_handshake_message unk t htype) (ps_whole_length_pred (ps_whole_ctls_transcript_handshake_message unk t htype) length))

noeq
type ctls_transcript_handshake (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (t:ctls_template bytes) = {
  msg_type: handshake_type;
  length: nat_lbytes 3;
  msg: fixed_length_ctls_transcript_handshake_message bytes unk t msg_type length;
}

%splice [ps_ctls_transcript_handshake] (gen_parser (`ctls_transcript_handshake))
