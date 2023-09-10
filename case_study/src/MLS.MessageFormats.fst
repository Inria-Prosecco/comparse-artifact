module MLS.MessageFormats

open Comparse

let mls_nat_pred (n:nat) = n < normalize_term (pow2 30)
let mls_nat_pred_eq (n:nat): Lemma(pow2 30 == normalize_term (pow2 30)) [SMTPat (mls_nat_pred n)] =
  assert_norm(pow2 30 == normalize_term (pow2 30))
type mls_nat = refined nat mls_nat_pred
val ps_mls_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes mls_nat_pred
let ps_mls_nat #bytes #bl =
  mk_trivial_isomorphism (refine ps_quic_nat mls_nat_pred)

val ps_mls_nat_length:
  #bytes:Type0 -> {| bytes_like bytes |} ->
  x:mls_nat ->
  Lemma (
    prefixes_length #bytes (ps_mls_nat.serialize x) == (
      if x < pow2 6 then 1
      else if x < pow2 14 then 2
      else 4
    ) /\
    pow2 6 == normalize_term (pow2 6) /\
    pow2 14 == normalize_term (pow2 14)
  )
  [SMTPat (prefixes_length #bytes (ps_mls_nat.serialize x))]
let ps_mls_nat_length #bytes #bl x = ()

type mls_bytes (bytes:Type0) {|bytes_like bytes|} = pre_length_bytes bytes mls_nat_pred
type mls_list (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_list ps_a mls_nat_pred

let ps_mls_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes (mls_bytes bytes) = ps_pre_length_bytes mls_nat_pred ps_mls_nat
let ps_mls_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (mls_list bytes ps_a) = ps_pre_length_list #bytes mls_nat_pred ps_mls_nat ps_a

let mls_ascii_string_pred (s:ascii_string): bool = mls_nat_pred (FStar.String.strlen s)
type mls_ascii_string = refined ascii_string mls_ascii_string_pred
let ps_mls_ascii_string (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes mls_ascii_string =
  length_prefix_ps_whole mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred)

val ps_mls_ascii_string_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:mls_ascii_string ->
  Lemma (
    prefixes_length #bytes (ps_mls_ascii_string.serialize x) ==
      prefixes_length #bytes (ps_mls_nat.serialize (String.strlen x)) +
      String.strlen x
  )
  [SMTPat (prefixes_length #bytes (ps_mls_ascii_string.serialize x))]
let ps_mls_ascii_string_length #bytes #bl x =
  length_prefix_ps_whole_length #bytes mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred) x

val ps_mls_ascii_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  x:mls_ascii_string ->
  Lemma (is_well_formed_prefix ps_mls_ascii_string pre x)
  [SMTPat (is_well_formed_prefix ps_mls_ascii_string pre x)]
let ps_mls_ascii_string_is_well_formed #bytes #bl pre x =
  assert(is_well_formed_whole ps_whole_ascii_string pre x);
  length_prefix_ps_whole_is_well_formed #bytes mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred) pre x

/// opaque HPKEPublicKey<V>;

type hpke_public_key (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_hpke_public_key] (gen_parser (`hpke_public_key))

/// enum {
///     reserved(0),
///     mls10(1),
///     (255)
/// } ProtocolVersion;

type protocol_version =
  | [@@@ with_num_tag 2 0] PV_mls_reserved: protocol_version
  | [@@@ with_num_tag 2 1] PV_mls10: protocol_version
  | [@@@ open_tag] PV_unknown: n:nat_lbytes 2{~(n <= 1)} -> protocol_version

%splice [ps_protocol_version] (gen_parser (`protocol_version))

/// uint16 CipherSuite;

type cipher_suite =
  | [@@@ with_num_tag 2 0x0000] CS_reserved: cipher_suite
  | [@@@ with_num_tag 2 0x0001] CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519: cipher_suite
  | [@@@ with_num_tag 2 0x0002] CS_mls_128_dhkemp256_aes128gcm_sha256_p256: cipher_suite
  | [@@@ with_num_tag 2 0x0003] CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519: cipher_suite
  | [@@@ with_num_tag 2 0x0004] CS_mls_256_dhkemx448_aes256gcm_sha512_ed448: cipher_suite
  | [@@@ with_num_tag 2 0x0005] CS_mls_256_dhkemp521_aes256gcm_sha512_p521: cipher_suite
  | [@@@ with_num_tag 2 0x0006] CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448: cipher_suite
  | [@@@ with_num_tag 2 0x0007] CS_mls_256_dhkemp384_aes256gcm_sha384_p384: cipher_suite
  | [@@@ open_tag] CS_unknown: n:nat_lbytes 2{~(n <= 7)} -> cipher_suite

%splice [ps_cipher_suite] (gen_parser (`cipher_suite))

/// // See IANA registry for registered values
/// uint16 ExtensionType;

type extension_type: eqtype =
  | [@@@ with_num_tag 2 0x0000] ET_reserved: extension_type
  | [@@@ with_num_tag 2 0x0001] ET_application_id: extension_type
  | [@@@ with_num_tag 2 0x0002] ET_ratchet_tree: extension_type
  | [@@@ with_num_tag 2 0x0003] ET_required_capabilities: extension_type
  | [@@@ with_num_tag 2 0x0004] ET_external_pub: extension_type
  | [@@@ with_num_tag 2 0x0005] ET_external_senders: extension_type
  | [@@@ open_tag] ET_unknown: n:nat_lbytes 2{~(n <= 5)} -> extension_type

%splice [ps_extension_type] (gen_parser (`extension_type))

/// struct {
///     ExtensionType extension_type;
///     opaque extension_data<V>;
/// } Extension;

type extension (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type;
  extension_data: mls_bytes bytes;
}

%splice [ps_extension] (gen_parser (`extension))

/// struct {
///     uint8 present;
///     select (present) {
///         case 0: struct{};
///         case 1: T value;
///     }
/// } optional<T>;

[@@"opaque_to_smt"]
val ps_option:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  parser_serializer bytes a ->
  parser_serializer bytes (option a)
let ps_option #bytes #bl #a ps_a =
  let n_pred = (fun n -> n <= 1) in
  let b_type (x:refined (nat_lbytes 1) n_pred): Type0 =
    if x = 1 then a else unit
  in
  mk_isomorphism (option a)
    (
      bind #_ #_ #_ #b_type (refine (ps_nat_lbytes 1) n_pred) (fun present ->
        if present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match present with
    | 0 -> None
    | 1 -> Some x
  )
  (fun x -> match x with
    | None -> (|0, ()|)
    | Some x -> (|1, x|)
  )

val ps_option_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  ps_a:parser_serializer bytes a -> x:option a ->
  Lemma (
    prefixes_length ((ps_option ps_a).serialize x) == (
      match x with
      | None -> 1
      | Some y -> 1 + prefixes_length (ps_a.serialize y)
    )
  )
  [SMTPat (prefixes_length ((ps_option ps_a).serialize x))]
let ps_option_length #bytes #bl #a ps_a x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

val ps_option_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  ps_a:parser_serializer bytes a -> pre:bytes_compatible_pre bytes -> x:option a ->
  Lemma (
    is_well_formed_prefix (ps_option ps_a) pre x <==> (
      match x with
      | None -> True
      | Some y -> is_well_formed_prefix ps_a pre y
    )
  )
  [SMTPat (is_well_formed_prefix (ps_option ps_a) pre x)]
let ps_option_is_well_formed #bytes #bl #a ps_a pre x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

// Special "option" type, when we know statically whether it is a "Some" or "None"

let static_option (b:bool) (a:Type): Type =
  if b then a else unit

val ps_static_option:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  b:bool -> parser_serializer_prefix bytes a ->
  parser_serializer_prefix bytes (static_option b a)
let ps_static_option #bytes #bl #a b ps_a =
  if b then ps_a else ps_unit

val mk_static_option: #b:bool -> #a:Type -> a -> static_option b a
let mk_static_option #b #a x =
  if b then x else ()

/// struct {
///     ProtocolVersion version = mls10;
///     CipherSuite cipher_suite;
///     opaque group_id<V>;
///     uint64 epoch;
///     opaque tree_hash<V>;
///     opaque confirmed_transcript_hash<V>;
///     Extension extensions<V>;
/// } GroupContext;

type group_context (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version;
  cipher_suite: cipher_suite;
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  tree_hash: mls_bytes bytes;
  confirmed_transcript_hash: mls_bytes bytes;
  extensions: mls_list bytes ps_extension;
}

%splice [ps_group_context] (gen_parser (`group_context))

(*** Proposals ***)

/// uint16 ProposalType;

// Defined here because needed in TreeSync's proposal list in leaf node capabilities
// Actual sum type defined in TreeDEM.NetworkTypes
type proposal_type =
  | [@@@ with_num_tag 2 0x0000] PT_reserved: proposal_type
  | [@@@ with_num_tag 2 0x0001] PT_add: proposal_type
  | [@@@ with_num_tag 2 0x0002] PT_update: proposal_type
  | [@@@ with_num_tag 2 0x0003] PT_remove: proposal_type
  | [@@@ with_num_tag 2 0x0004] PT_psk: proposal_type
  | [@@@ with_num_tag 2 0x0005] PT_reinit: proposal_type
  | [@@@ with_num_tag 2 0x0006] PT_external_init: proposal_type
  | [@@@ with_num_tag 2 0x0007] PT_group_context_extensions: proposal_type
  | [@@@ open_tag] PT_unknown: n:nat_lbytes 2{~(n <= 7)} -> proposal_type

%splice [ps_proposal_type] (gen_parser (`proposal_type))

(*** TreeSync ***)

noeq type treekem_types (bytes:Type0) {|bytes_like bytes|} = {
  leaf_content: leaf_content:Type0{hasEq bytes ==> hasEq leaf_content};
  node_content: node_content:Type0{hasEq bytes ==> hasEq node_content};
  ps_leaf_content: parser_serializer bytes leaf_content;
  ps_node_content: parser_serializer bytes node_content;
}

/// opaque SignaturePublicKey<V>;

type signature_public_key (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_signature_public_key] (gen_parser (`signature_public_key))

/// // See IANA registry for registered values
/// uint16 CredentialType;

type credential_type =
  | [@@@ with_num_tag 2 0x0000] CT_reserved: credential_type
  | [@@@ with_num_tag 2 0x0001] CT_basic: credential_type
  | [@@@ with_num_tag 2 0x0002] CT_x509: credential_type
  | [@@@ open_tag] CT_unknown: n:nat_lbytes 2{~(n <= 2)} -> credential_type

%splice [ps_credential_type] (gen_parser (`credential_type))

/// struct {
///     opaque cert_data<V>;
/// } Certificate;

type certificate (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_certificate] (gen_parser (`certificate))

/// struct {
///     CredentialType credential_type;
///     select (Credential.credential_type) {
///         case basic:
///             opaque identity<V>;
///
///         case x509:
///             Certificate chain<V>;
///     };
/// } Credential;

type credential (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag CT_basic] C_basic: identity: mls_bytes bytes -> credential bytes
  | [@@@ with_tag CT_x509] C_x509: chain: mls_list bytes ps_certificate -> credential bytes

%splice [ps_credential] (gen_parser (`credential))

/// enum {
///     reserved(0),
///     key_package(1),
///     update(2),
///     commit(3),
///     (255)
/// } LeafNodeSource;

type leaf_node_source =
  | [@@@ with_num_tag 1 1] LNS_key_package: leaf_node_source
  | [@@@ with_num_tag 1 2] LNS_update:      leaf_node_source
  | [@@@ with_num_tag 1 3] LNS_commit:      leaf_node_source

%splice [ps_leaf_node_source] (gen_parser (`leaf_node_source))

/// struct {
///     ProtocolVersion versions<V>;
///     CipherSuite ciphersuites<V>;
///     ExtensionType extensions<V>;
///     ProposalType proposals<V>;
///     CredentialType credentials<V>;
/// } Capabilities;

type capabilities (bytes:Type0) {|bytes_like bytes|} = {
  versions: mls_list bytes ps_protocol_version;
  ciphersuites: mls_list bytes ps_cipher_suite;
  extensions: mls_list bytes ps_extension_type;
  proposals: mls_list bytes ps_proposal_type;
  credentials: mls_list bytes ps_credential_type;
}

%splice [ps_capabilities] (gen_parser (`capabilities))

/// struct {
///     uint64 not_before;
///     uint64 not_after;
/// } Lifetime;

type lifetime = {
  not_before: nat_lbytes 8;
  not_after: nat_lbytes 8;
}

%splice [ps_lifetime] (gen_parser (`lifetime))

/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNode.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///     // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
///     opaque signature<V>;
/// } LeafNode;

type leaf_node_data (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_leaf_content]
  content: tkt.leaf_content; //encryption key
  signature_key: signature_public_key bytes;
  credential: credential bytes;
  capabilities: capabilities bytes;
  source: leaf_node_source;
  [@@@ with_parser #bytes (ps_static_option (source = LNS_key_package) ps_lifetime)]
  lifetime: static_option (source = LNS_key_package) lifetime;
  [@@@ with_parser #bytes (ps_static_option (source = LNS_commit) ps_mls_bytes)]
  parent_hash: static_option (source = LNS_commit) (mls_bytes bytes);
  extensions: mls_list bytes ps_extension;
}

%splice [ps_leaf_node_data] (gen_parser (`leaf_node_data))

type leaf_node (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data bytes tkt;
  signature: mls_bytes bytes;
}

%splice [ps_leaf_node] (gen_parser (`leaf_node))

/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             struct{};
///
///         case update:
///             opaque group_id<V>;
///
///         case commit:
///             opaque group_id<V>;
///     }
/// } LeafNodeTBS;

type leaf_node_tbs (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data bytes tkt;
  [@@@ with_parser #bytes (ps_static_option (data.source = LNS_update || data.source = LNS_commit) ps_mls_bytes)]
  group_id: static_option (data.source = LNS_update || data.source = LNS_commit) (mls_bytes bytes);
  [@@@ with_parser #bytes (ps_static_option (data.source = LNS_update || data.source = LNS_commit) (ps_nat_lbytes 4))]
  leaf_index: static_option (data.source = LNS_update || data.source = LNS_commit) (nat_lbytes 4);
}

%splice [ps_leaf_node_tbs] (gen_parser (`leaf_node_tbs))

/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
/// } KeyPackageTBS;

type key_package_tbs (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  version: protocol_version;
  cipher_suite: cipher_suite;
  init_key: hpke_public_key bytes;
  leaf_node: leaf_node bytes tkt;
  extensions: mls_list bytes ps_extension;
}

%splice [ps_key_package_tbs] (gen_parser (`key_package_tbs))

/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
///     // SignWithLabel(., "KeyPackageTBS", KeyPackageTBS)
///     opaque signature<V>;
/// } KeyPackage;

type key_package (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  tbs: key_package_tbs bytes tkt;
  signature: mls_bytes bytes;
}

%splice [ps_key_package] (gen_parser (`key_package))

/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
///     uint32 unmerged_leaves<V>;
/// } ParentNode;

type parent_node (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_node_content]
  content: tkt.node_content; //encryption_key
  parent_hash: mls_bytes bytes;
  unmerged_leaves: mls_list bytes (ps_nat_lbytes #bytes 4);
}

%splice [ps_parent_node] (gen_parser (`parent_node))

/// enum {
///     reserved(0),
///     leaf(1),
///     parent(2),
///     (255)
/// } NodeType;

type node_type =
  | [@@@ with_num_tag 1 1] NT_leaf: node_type
  | [@@@ with_num_tag 1 2] NT_parent: node_type

%splice [ps_node_type] (gen_parser (`node_type))

/// struct {
///     NodeType node_type;
///     select (Node.node_type) {
///         case leaf:   LeafNode leaf_node;
///         case parent: ParentNode parent_node;
///     };
/// } Node;

type node (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  | [@@@ with_tag NT_leaf] N_leaf: leaf_node bytes tkt -> node bytes tkt
  | [@@@ with_tag NT_parent] N_parent: parent_node bytes tkt -> node bytes tkt

%splice [ps_node] (gen_parser (`node))

/// optional<Node> ratchet_tree<V>;

type ratchet_tree (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = mls_list bytes (ps_option (ps_node tkt))

%splice [ps_ratchet_tree] (gen_parser (`ratchet_tree))
(*** TreeKEM ***)

val tkt: #bytes:Type0 -> {|bytes_like bytes|} -> treekem_types bytes
let tkt #bytes #bl = {
  leaf_content = hpke_public_key bytes;
  node_content = hpke_public_key bytes;
  ps_leaf_content = ps_hpke_public_key;
  ps_node_content = ps_hpke_public_key;
}

/// struct {
///     opaque kem_output<V>;
///     opaque ciphertext<V>;
/// } HPKECiphertext;

type hpke_ciphertext (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_hpke_ciphertext] (gen_parser (`hpke_ciphertext))

/// struct {
///     HPKEPublicKey encryption_key;
///     HPKECiphertext encrypted_path_secret<V>;
/// } UpdatePathNode;

type update_path_node (bytes:Type0) {|bytes_like bytes|} = {
  encryption_key: hpke_public_key bytes;
  encrypted_path_secret: mls_list bytes ps_hpke_ciphertext;
}

%splice [ps_update_path_node] (gen_parser (`update_path_node))

/// struct {
///     LeafNode leaf_node;
///     UpdatePathNode nodes<V>;
/// } UpdatePath;

type update_path (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node bytes tkt;
  nodes: mls_list bytes ps_update_path_node;
}

%splice [ps_update_path] (gen_parser (`update_path))

(*** PSKs ***)

(*** PSKs ***)

/// enum {
///   reserved(0),
///   external(1),
///   resumption(2),
///   (255)
/// } PSKType;

type psk_type =
  | [@@@ with_num_tag 1 1] PSKT_external: psk_type
  | [@@@ with_num_tag 1 2] PSKT_resumption: psk_type

%splice [ps_psk_type] (gen_parser (`psk_type))

/// enum {
///   reserved(0),
///   application(1),
///   reinit(2),
///   branch(3),
///   (255)
/// } ResumptionPSKUsage;

type resumption_psk_usage =
  | [@@@ with_num_tag 1 1] RPSKU_application: resumption_psk_usage
  | [@@@ with_num_tag 1 2] RPSKU_reinit: resumption_psk_usage
  | [@@@ with_num_tag 1 3] RPSKU_branch: resumption_psk_usage

%splice [ps_resumption_psk_usage] (gen_parser (`resumption_psk_usage))

/// struct {
///   PSKType psktype;
///   select (PreSharedKeyID.psktype) {
///     case external:
///       opaque psk_id<V>;
///
///     case resumption:
///       ResumptionPSKUsage usage;
///       opaque psk_group_id<V>;
///       uint64 psk_epoch;
///   };
///   opaque psk_nonce<V>;
/// } PreSharedKeyID;

type pre_shared_key_id (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PSKT_external] PSKI_external: psk_id:mls_bytes bytes -> psk_nonce:mls_bytes bytes -> pre_shared_key_id bytes
  | [@@@ with_tag PSKT_resumption] PSKI_resumption: usage: resumption_psk_usage -> psk_group_id:mls_bytes bytes -> psk_epoch:nat_lbytes 8 -> psk_nonce:mls_bytes bytes -> pre_shared_key_id bytes

%splice [ps_pre_shared_key_id] (gen_parser (`pre_shared_key_id))

/// struct {
///     PreSharedKeyID id;
///     uint16 index;
///     uint16 count;
/// } PSKLabel;

type psk_label (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

%splice [ps_psk_label] (gen_parser (`psk_label))

(*** Proposals ***)

/// struct {
///     KeyPackage key_package;
/// } Add;

type add (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package bytes tkt;
}

%splice [ps_add] (gen_parser (`add))

/// struct {
///     LeafNode leaf_node;
/// } Update;

type update (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node bytes tkt;
}

%splice [ps_update] (gen_parser (`update))

/// struct {
///     uint32 removed;
/// } Remove;

type remove (bytes:Type0) {|bytes_like bytes|} = {
  removed: nat_lbytes 4;
}

%splice [ps_remove] (gen_parser (`remove))

/// struct {
///     PreSharedKeyID psk;
/// } PreSharedKey;

type pre_shared_key (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id bytes;
}

%splice [ps_pre_shared_key] (gen_parser (`pre_shared_key))

/// struct {
///     opaque group_id<V>;
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     Extension extensions<V>;
/// } ReInit;

type reinit (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  version: protocol_version;
  cipher_suite: cipher_suite;
  extensions: mls_list bytes ps_extension
}

%splice [ps_reinit] (gen_parser (`reinit))

/// struct {
///   opaque kem_output<V>;
/// } ExternalInit;

type external_init (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes
}

%splice [ps_external_init] (gen_parser (`external_init))

/// struct {
///   Extension extensions<V>;
/// } GroupContextExtensions;

type group_context_extensions (bytes:Type0) {|bytes_like bytes|} = {
  extensions: mls_list bytes ps_extension;
}

%splice [ps_group_context_extensions] (gen_parser (`group_context_extensions))

(*** Refs ***)

/// opaque HashReference<V>;
///
/// HashReference KeyPackageRef;
/// HashReference ProposalRef;

type key_package_ref (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_key_package_ref] (gen_parser (`key_package_ref))

type proposal_ref (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_proposal_ref] (gen_parser (`proposal_ref))

(*** Message framing ***)

/// // See IANA registry for registered values
/// uint16 ProposalType;

type proposal (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PT_add] P_add: add bytes -> proposal bytes
  | [@@@ with_tag PT_update] P_update: update bytes -> proposal bytes
  | [@@@ with_tag PT_remove] P_remove: remove bytes -> proposal bytes
  | [@@@ with_tag PT_psk] P_psk: pre_shared_key bytes -> proposal bytes
  | [@@@ with_tag PT_reinit] P_reinit: reinit bytes -> proposal bytes
  | [@@@ with_tag PT_external_init] P_external_init: external_init bytes -> proposal bytes
  | [@@@ with_tag PT_group_context_extensions] P_group_context_extensions: group_context_extensions bytes -> proposal bytes

%splice [ps_proposal] (gen_parser (`proposal))

/// enum {
///   reserved(0),
///   proposal(1),
///   reference(2),
///   (255)
/// } ProposalOrRefType;
///
/// struct {
///   ProposalOrRefType type;
///   select (ProposalOrRef.type) {
///     case proposal:  Proposal proposal;
///     case reference: ProposalRef reference;
///   };
/// } ProposalOrRef;

type proposal_or_ref (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 1 1] POR_proposal: proposal bytes -> proposal_or_ref bytes
  | [@@@ with_num_tag 1 2] POR_reference: proposal_ref bytes -> proposal_or_ref bytes

%splice [ps_proposal_or_ref] (gen_parser (`proposal_or_ref))

/// struct {
///     ProposalOrRef proposals<V>;
///     optional<UpdatePath> path;
/// } Commit;

type commit (bytes:Type0) {|bytes_like bytes|} = {
  proposals: mls_list bytes ps_proposal_or_ref;
  [@@@ with_parser #bytes (ps_option ps_update_path)]
  path: option (update_path bytes);
}

%splice [ps_commit] (gen_parser (`commit))

/// enum {
///     reserved(0),
///     member(1),
///     external(2),
///     new_member_proposal(3),
///     new_member_commit(4),
///     (255)
/// } SenderType;

type sender_type =
  | [@@@ with_num_tag 1 1] ST_member: sender_type
  | [@@@ with_num_tag 1 2] ST_external: sender_type
  | [@@@ with_num_tag 1 3] ST_new_member_proposal: sender_type
  | [@@@ with_num_tag 1 4] ST_new_member_commit: sender_type

%splice [ps_sender_type] (gen_parser (`sender_type))

/// struct {
///     SenderType sender_type;
///     select (Sender.sender_type) {
///         case member:
///             uint32 leaf_index;
///         case external:
///             uint32 sender_index;
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// } Sender;

type sender (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag ST_member] S_member: leaf_index:nat_lbytes 4 -> sender bytes
  | [@@@ with_tag ST_external] S_external: sender_index:nat_lbytes 4 -> sender bytes
  | [@@@ with_tag ST_new_member_proposal] S_new_member_proposal: sender bytes
  | [@@@ with_tag ST_new_member_commit] S_new_member_commit: sender bytes

%splice [ps_sender] (gen_parser (`sender))

/// // See IANA registry for registered values
/// uint16 WireFormat;

type wire_format =
  | [@@@ with_num_tag 2 0] WF_reserved: wire_format
  | [@@@ with_num_tag 2 1] WF_mls_public_message: wire_format
  | [@@@ with_num_tag 2 2] WF_mls_private_message: wire_format
  | [@@@ with_num_tag 2 3] WF_mls_welcome: wire_format
  | [@@@ with_num_tag 2 4] WF_mls_group_info: wire_format
  | [@@@ with_num_tag 2 5] WF_mls_key_package: wire_format
  | [@@@ open_tag] WF_unknown: n:nat_lbytes 2{~(n <= 5)} -> wire_format

%splice [ps_wire_format] (gen_parser (`wire_format))

/// opaque MAC<V>;

type mac (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_mac] (gen_parser (`mac))

/// enum {
///     reserved(0),
///     application(1),
///     proposal(2),
///     commit(3),
///     (255)
/// } ContentType;

type content_type =
  | [@@@ with_num_tag 1 1] CT_application: content_type
  | [@@@ with_num_tag 1 2] CT_proposal: content_type
  | [@@@ with_num_tag 1 3] CT_commit: content_type

%splice [ps_content_type] (gen_parser (`content_type))

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     Sender sender;
///     opaque authenticated_data<V>;
///
///     ContentType content_type;
///     select (FramedContent.content_type) {
///         case application:
///           opaque application_data<V>;
///         case proposal:
///           Proposal proposal;
///         case commit:
///           Commit commit;
///     };
/// } FramedContent;

val mls_untagged_content: bytes:Type0 -> {|bytes_like bytes|} -> content_type -> Type0
let mls_untagged_content bytes #bl content_type =
  match content_type with
  | CT_application -> mls_bytes bytes
  | CT_proposal -> proposal bytes
  | CT_commit -> commit bytes

%splice [ps_mls_untagged_content] (gen_parser (`mls_untagged_content))

type mls_tagged_content (bytes:Type0) {|bytes_like bytes|} = {
  content_type: content_type;
  content: mls_untagged_content bytes content_type;
}

%splice [ps_mls_tagged_content] (gen_parser (`mls_tagged_content))

type framed_content (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  sender: sender bytes;
  authenticated_data: mls_bytes bytes;
  content: mls_tagged_content bytes;
}

%splice [ps_framed_content] (gen_parser (`framed_content))

/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     FramedContent content;
///     select (FramedContentTBS.content.sender.sender_type) {
///         case member:
///         case new_member_commit:
///             GroupContext context;
///         case external:
///         case new_member_proposal:
///             struct{};
///     };
/// } FramedContentTBS;

type framed_content_tbs (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version;
  wire_format: wire_format;
  content: framed_content bytes;
  [@@@ with_parser #bytes (ps_static_option (S_member? content.sender || S_new_member_commit? content.sender) ps_group_context)]
  group_context: static_option (S_member? content.sender || S_new_member_commit? content.sender) (group_context bytes);
}

%splice [ps_framed_content_tbs] (gen_parser (`framed_content_tbs))

/// struct {
///     /* SignWithLabel(., "FramedContentTBS", FramedContentTBS) */
///     opaque signature<V>;
///     select (FramedContent.content_type) {
///         case commit:
///             /*
///               MAC(confirmation_key,
///                   GroupContext.confirmed_transcript_hash)
///             */
///             MAC confirmation_tag;
///         case application:
///         case proposal:
///             struct{};
///     };
/// } FramedContentAuthData;

type framed_content_auth_data (bytes:Type0) {|bl:bytes_like bytes|} (content_type:content_type) = {
  signature: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_static_option (content_type = CT_commit) ps_mac)]
  confirmation_tag: static_option (content_type = CT_commit) (mac bytes);
}

%splice [ps_framed_content_auth_data] (gen_parser (`framed_content_auth_data))

/// struct {
///     WireFormat wire_format;
///     FramedContent content;
///     FramedContentAuthData auth;
/// } AuthenticatedContent;

type authenticated_content (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format;
  content: framed_content bytes;
  auth: framed_content_auth_data bytes content.content.content_type;
}

%splice [ps_authenticated_content] (gen_parser (`authenticated_content))

/// struct {
///   FramedContentTBS content_tbs;
///   FramedContentAuthData auth;
/// } AuthenticatedContentTBM;

type authenticated_content_tbm (bytes:Type0) {|bytes_like bytes|} = {
  content_tbs: framed_content_tbs bytes;
  auth: framed_content_auth_data bytes content_tbs.content.content.content_type;
}

%splice [ps_authenticated_content_tbm] (gen_parser (`authenticated_content_tbm))

/// struct {
///     FramedContent content;
///     FramedContentAuthData auth;
///     select (PublicMessage.content.sender.sender_type) {
///         case member:
///             MAC membership_tag;
///         case external:
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// } PublicMessage;

type public_message (bytes:Type0) {|bytes_like bytes|} = {
  content: framed_content bytes;
  auth: framed_content_auth_data bytes content.content.content_type;
  [@@@with_parser #bytes (ps_static_option (S_member? content.sender) ps_mac)]
  membership_tag: static_option (S_member? content.sender) (mac bytes);
}

%splice [ps_public_message] (gen_parser (`public_message))

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
///     opaque encrypted_sender_data<V>;
///     opaque ciphertext<V>;
/// } PrivateMessage;

type private_message (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type;
  authenticated_data: mls_bytes bytes;
  encrypted_sender_data: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_private_message] (gen_parser (`private_message))

/// struct {
///     select (PrivateMessage.content_type) {
///         case application:
///           opaque application_data<V>;
///
///         case proposal:
///           Proposal proposal;
///
///         case commit:
///           Commit commit;
///     };
///
///     FramedContentAuthData auth;
///     opaque padding[length_of_padding];
/// } PrivateMessageContent;

type private_message_content_data (bytes:Type0) {|bytes_like bytes|} (content_type: content_type) = {
  content: mls_untagged_content bytes content_type;
  auth: framed_content_auth_data bytes content_type;
}

%splice [ps_private_message_content_data] (gen_parser (`private_message_content_data))

let is_nat_zero (n:nat_lbytes 1) = n = 0
let zero_byte = refined (nat_lbytes 1) is_nat_zero
let ps_zero_byte (#bytes:Type0) {|bytes_like bytes|} = refine #bytes (ps_nat_lbytes 1) is_nat_zero

type private_message_content (bytes:Type0) {|bytes_like bytes|} (content_type: content_type) = {
  data: private_message_content_data bytes content_type;
  padding: list zero_byte;
}

val pse_private_message_content: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type -> parser_serializer_whole bytes (private_message_content bytes content_type)
let pse_private_message_content #bytes #bl content_type =
  let iso = mk_isomorphism_between
    (fun (|data, padding|) -> {data; padding})
    (fun {data; padding} -> (|data, padding|))
  in
  isomorphism_whole
    (bind_whole (ps_private_message_content_data content_type) (fun _ -> ps_whole_list ps_zero_byte))
    iso

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
/// } PrivateContentAAD;

type private_content_aad (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type;
  authenticated_data: mls_bytes bytes;
}

%splice [ps_private_content_aad] (gen_parser (`private_content_aad))

/// struct {
///     uint32 leaf_index;
///     uint32 generation;
///     opaque reuse_guard[4];
/// } SenderData;

type sender_data (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

%splice [ps_sender_data] (gen_parser (`sender_data))

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
/// } SenderDataAAD;

type sender_data_aad (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type;
}

%splice [ps_sender_data_aad] (gen_parser (`sender_data_aad))

/// struct {
///     WireFormat wire_format;
///     FramedContent content; /* with content_type == commit */
///     opaque signature<V>;
/// } ConfirmedTranscriptHashInput;

type confirmed_transcript_hash_input (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format;
  content: framed_content bytes;
  signature: mls_bytes bytes;
}

%splice [ps_confirmed_transcript_hash_input] (gen_parser (`confirmed_transcript_hash_input))

/// struct {
///     MAC confirmation_tag;
/// } InterimTranscriptHashInput;

type interim_transcript_hash_input (bytes:Type0) {|bytes_like bytes|} = {
  confirmation_tag: mac bytes;
}

%splice [ps_interim_transcript_hash_input] (gen_parser (`interim_transcript_hash_input))

/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
/// } GroupInfoTBS;

type group_info_tbs (bytes:Type0) {|bytes_like bytes|} = {
  group_context: group_context bytes;
  extensions: mls_bytes bytes;
  confirmation_tag: mac bytes;
  signer: nat_lbytes 4;
}

%splice [ps_group_info_tbs] (gen_parser (`group_info_tbs))

/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
///     /* SignWithLabel(., "GroupInfoTBS", GroupInfoTBS) */
///     opaque signature<V>;
/// } GroupInfo;

type group_info (bytes:Type0) {|bytes_like bytes|} = {
  tbs: group_info_tbs bytes;
  signature: mls_bytes bytes;
}

%splice [ps_group_info] (gen_parser (`group_info))


/// struct {
///   opaque path_secret<V>;
/// } PathSecret;

type path_secret (bytes:Type0) {|bytes_like bytes|} = {
  path_secret_: mls_bytes bytes;
}

%splice [ps_path_secret] (gen_parser (`path_secret))

/// struct {
///   opaque joiner_secret<V>;
///   optional<PathSecret> path_secret;
///   PreSharedKeyID psks<V>;
/// } GroupSecrets;

type group_secrets (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_option ps_path_secret)]
  path_secret: option (path_secret bytes);
  psks: mls_list bytes (ps_pre_shared_key);
}

%splice [ps_group_secrets] (gen_parser (`group_secrets))

/// struct {
///   KeyPackageRef new_member;
///   HPKECiphertext encrypted_group_secrets;
/// } EncryptedGroupSecrets;

type encrypted_group_secrets (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref bytes;
  encrypted_group_secrets_: hpke_ciphertext bytes;
}

%splice [ps_encrypted_group_secrets] (gen_parser (`encrypted_group_secrets))

/// struct {
///   CipherSuite cipher_suite;
///   EncryptedGroupSecrets secrets<V>;
///   opaque encrypted_group_info<V>;
/// } Welcome;

type welcome (bytes:Type0) {|bytes_like bytes|} = {
  cipher_suite: cipher_suite;
  secrets: mls_list bytes ps_encrypted_group_secrets;
  encrypted_group_info: mls_bytes bytes;
}

%splice [ps_welcome] (gen_parser (`welcome))

/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     select (MLSMessage.wire_format) {
///         case mls_public_message:
///             PublicMessage public_message;
///         case mls_private_message:
///             PrivateMessage private_message;
///         case mls_welcome:
///             Welcome welcome;
///         case mls_group_info:
///             GroupInfo group_info;
///         case mls_key_package:
///             KeyPackage key_package;
///     };
/// } MLSMessage;

type mls_10_message (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag WF_mls_public_message] M_public_message: public_message bytes -> mls_10_message bytes
  | [@@@ with_tag WF_mls_private_message] M_private_message: private_message bytes -> mls_10_message bytes
  | [@@@ with_tag WF_mls_welcome] M_welcome: welcome bytes -> mls_10_message bytes
  | [@@@ with_tag WF_mls_group_info] M_group_info: group_info bytes -> mls_10_message bytes
  | [@@@ with_tag WF_mls_key_package] M_key_package: key_package bytes tkt -> mls_10_message bytes

%splice [ps_mls_10_message] (gen_parser (`mls_10_message))

type mls_message (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PV_mls10] M_mls10: mls_10_message bytes -> mls_message bytes

%splice [ps_mls_message] (gen_parser (`mls_message))

(*** Cryptography inputs ***)

/// struct {
///     opaque label<V>;
///     opaque content<V>;
/// } SignContent;

type sign_content (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  content: mls_bytes bytes;
}

%splice [ps_sign_content] (gen_parser (`sign_content))

/// struct {
///     uint16 length;
///     opaque label<V>;
///     opaque context<V>;
/// } KDFLabel;

type kdf_label (bytes:Type0) {|bytes_like bytes|} = {
  length: nat_lbytes 2;
  label: mls_bytes bytes;
  context: mls_bytes bytes;
}

%splice [ps_kdf_label] (gen_parser (`kdf_label))

/// struct {
///   opaque label<V>;
///   opaque context<V>;
/// } EncryptContext;

type encrypt_context (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  context: mls_bytes bytes;
}

%splice[ps_encrypt_context] (gen_parser (`encrypt_context))

/// struct {
///   opaque label<V>;
///   opaque value<V>;
/// } RefHashInput;

type ref_hash_input (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  value: mls_bytes bytes;
}

%splice [ps_ref_hash_input] (gen_parser (`ref_hash_input))

/// struct {
///     uint32 leaf_index;
///     optional<LeafNode> leaf_node;
/// } LeafNodeHashInput;

type leaf_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  leaf_index: nat_lbytes 4;
  [@@@ with_parser #bytes (ps_option (ps_leaf_node tkt))]
  leaf_node: option (leaf_node bytes tkt);
}

%splice [ps_leaf_node_tree_hash_input] (gen_parser (`leaf_node_tree_hash_input))

/// struct {
///     optional<ParentNode> parent_node;
///     opaque left_hash<V>;
///     opaque right_hash<V>;
/// } ParentNodeHashInput;

type parent_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser #bytes (ps_option (ps_parent_node tkt))]
  parent_node: option (parent_node bytes tkt);
  left_hash: mls_bytes bytes;
  right_hash: mls_bytes bytes;
}

%splice [ps_parent_node_tree_hash_input] (gen_parser (`parent_node_tree_hash_input))

/// struct {
///   NodeType node_type;
///   select (TreeHashInput.node_type) {
///     case leaf:   LeafNodeHashInput leaf_node;
///     case parent: ParentNodeHashInput parent_node;
///   };
/// } TreeHashInput;

type tree_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  | [@@@ with_tag NT_leaf] LeafTreeHashInput: leaf_node: leaf_node_tree_hash_input bytes tkt -> tree_hash_input bytes tkt
  | [@@@ with_tag NT_parent] ParentTreeHashInput: parent_node: parent_node_tree_hash_input bytes tkt -> tree_hash_input bytes tkt

%splice [ps_tree_hash_input] (gen_parser (`tree_hash_input))

/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
///     opaque original_sibling_tree_hash<V>;
/// } ParentHashInput;

type parent_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_node_content]
  content: tkt.node_content; //encryption_key
  parent_hash: mls_bytes bytes;
  original_sibling_tree_hash: mls_bytes bytes;
}

%splice [ps_parent_hash_input] (gen_parser (`parent_hash_input))
