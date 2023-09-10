module CTLS.Transcript

open Comparse
open TLS13.MessageFormats
open CTLS.Profile
open CTLS.MessageFormats
open CTLS.Compressions

#set-options "--fuel 1 --ifuel 1"

(*** Mutual Auth compression ***)

val get_mutual_auth_template: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_template bytes -> option (ctls_mutual_auth_template bytes)
let get_mutual_auth_template #bytes #bl t =
  get_template_element ps_ctls_mutual_auth_template CTLSTET_mutual_auth t

type certificate_request_length_bounded (bytes:Type0) {|bytes_like bytes|} =
  cr:certificate_request bytes{length #bytes ((ps_prefix_to_ps_whole ps_certificate_request).serialize cr) < pow2 24}

#push-options "--fuel 2 --ifuel 1"
val mutual_auth_compute_cert_request:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_scheme ->
  certificate_request_length_bounded bytes
let mutual_auth_compute_cert_request #bytes #bl scheme =
  let expected_extension: extension bytes = {
    extension_type = ET_signature_algorithms;
    extension_data = ((ps_prefix_to_ps_whole #bytes ps_signature_scheme_list).serialize {
      supported_signature_algorithms = [scheme];
    });
  } in
  {
    certificate_request_context = Comparse.empty #bytes;
    extensions = [expected_extension];
  }
#pop-options

val mutual_auth_compress_internal:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  certificate_request_length_bounded bytes -> list (handshake bytes) ->
  option (list (handshake bytes))
let rec mutual_auth_compress_internal #bytes #bl expected_cr l =
  match l with
  | [] -> Some []
  | h1::t1 -> (
    if not (h1.msg_type = HT_encrypted_extensions) then (
      let? new_t1 = mutual_auth_compress_internal expected_cr t1 in
      Some (h1::new_t1)
    ) else (
      match t1 with
      | [] -> None
      | h2::t2 -> (
        if not (h2.msg_type = HT_certificate_request) then (
          None
        ) else if not (Nil? t2 || (Cons?.hd t2).msg_type <> HT_certificate_request) then (
          None
        ) else if not (h2.msg = expected_cr) then (
          Some l
        ) else (
          Some (h1::t2)
        )
      )
    )
  )

val mutual_auth_decompress_internal:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  certificate_request_length_bounded bytes -> list (handshake bytes) ->
  option (list (handshake bytes))
let rec mutual_auth_decompress_internal #bytes #bl expected_cr l =
  match l with
  | [] -> Some []
  | h1::t1 -> (
    if not (h1.msg_type = HT_encrypted_extensions) then (
      let? new_t1 = mutual_auth_decompress_internal expected_cr t1 in
      Some (h1::new_t1)
    ) else (
      let expected_cr_length = length ((ps_prefix_to_ps_whole ps_certificate_request).serialize expected_cr) in
      let msg: handshake bytes = { msg_type = HT_certificate_request; length = expected_cr_length; msg = expected_cr; } in
      match t1 with
      | [] -> Some [h1; msg]
      | h2::t2 -> (
        if not (h2.msg_type = HT_certificate_request) then (
          Some (h1::msg::t1)
        ) else if not (h2.msg <> expected_cr) then (
          None
        ) else if not (Nil? t2 || (Cons?.hd t2).msg_type <> HT_certificate_request) then (
          None
        ) else (
          Some l
        )
      )
    )
  )

val mutual_auth_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ctls_template bytes -> list (handshake bytes) ->
  option (list (handshake bytes))
let mutual_auth_compress #bytes #bl t l =
  match get_mutual_auth_template t, get_signature_algorithm_template t with
  | Some mutual_auth, Some signature_algorithm -> (
    if mutual_auth = 0 then
      Some l
    else (
      let expected_cr = mutual_auth_compute_cert_request signature_algorithm.signature_scheme in
      mutual_auth_compress_internal expected_cr l
    )
  )
  | _, _ -> Some l

val mutual_auth_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ctls_template bytes -> list (handshake bytes) ->
  option (list (handshake bytes))
let mutual_auth_decompress #bytes #bl t l =
  match get_mutual_auth_template t, get_signature_algorithm_template t with
  | Some mutual_auth, Some signature_algorithm -> (
    if mutual_auth = 0 then
      Some l
    else (
      let expected_cr = mutual_auth_compute_cert_request signature_algorithm.signature_scheme in
      mutual_auth_decompress_internal expected_cr l
    )
  )
  | _, _ -> Some l

val mutual_auth_decompress_compress_internal:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_cr:certificate_request_length_bounded bytes -> l:list (handshake bytes) ->
  Lemma (
    match mutual_auth_compress_internal expected_cr l with
    | None -> True
    | Some compressed_l ->
      mutual_auth_decompress_internal expected_cr compressed_l == Some l
  )
let rec mutual_auth_decompress_compress_internal #bytes #bl expected_cr l =
  match l with
  | [] -> ()
  | h1::t1 -> (
    if not (h1.msg_type = HT_encrypted_extensions) then (
      let new_t1 = mutual_auth_compress_internal expected_cr t1 in
      mutual_auth_decompress_compress_internal expected_cr t1
    ) else (
      match t1 with
      | [] -> ()
      | h2::t2 -> ()
    )
  )

val mutual_auth_compress_decompress_internal:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_cr:certificate_request_length_bounded bytes -> l:list (handshake bytes) ->
  Lemma (
    match mutual_auth_decompress_internal expected_cr l with
    | None -> True
    | Some decompressed_l ->
      mutual_auth_compress_internal expected_cr decompressed_l == Some l
  )
let rec mutual_auth_compress_decompress_internal #bytes #bl expected_cr l =
  match l with
  | [] -> ()
  | h1::t1 -> (
    if not (h1.msg_type = HT_encrypted_extensions) then (
      let new_t1 = mutual_auth_decompress_internal expected_cr t1 in
      mutual_auth_compress_decompress_internal expected_cr t1
    ) else (
      let expected_cr_length = length ((ps_prefix_to_ps_whole ps_certificate_request).serialize expected_cr) in
      let msg: handshake bytes = { msg_type = HT_certificate_request; length = expected_cr_length; msg = expected_cr; } in
      match t1 with
      | [] -> ()
      | h2::t2 -> ()
    )
  )

val mutual_auth_decompress_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  t:ctls_template bytes -> l:list (handshake bytes) ->
  Lemma (
    match mutual_auth_compress t l with
    | None -> True
    | Some compressed_l ->
      mutual_auth_decompress t compressed_l == Some l
  )
let mutual_auth_decompress_compress #bytes #bl t l =
  match get_mutual_auth_template t, get_signature_algorithm_template t with
  | Some mutual_auth, Some signature_algorithm -> (
    if mutual_auth = 0 then ()
    else (
      let expected_cr = mutual_auth_compute_cert_request signature_algorithm.signature_scheme in
      mutual_auth_decompress_compress_internal expected_cr l
    )
  )
  | _, _ -> ()

val mutual_auth_compress_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  t:ctls_template bytes -> l:list (handshake bytes) ->
  Lemma (
    match mutual_auth_decompress t l with
    | None -> True
    | Some decompressed_l ->
      mutual_auth_compress t decompressed_l == Some l
  )
let mutual_auth_compress_decompress #bytes #bl t l =
  match get_mutual_auth_template t, get_signature_algorithm_template t with
  | Some mutual_auth, Some signature_algorithm -> (
    if mutual_auth = 0 then ()
    else (
      let expected_cr = mutual_auth_compute_cert_request signature_algorithm.signature_scheme in
      mutual_auth_compress_decompress_internal expected_cr l
    )
  )
  | _, _ -> ()

val list_equivalent_destruct:
  #a:Type ->
  eq:equivalence a -> l1:list a -> l2:list a ->
  Lemma
  (requires l1 `list_equivalent eq` l2)
  (ensures (
    match l1, l2 with
    | [], [] -> True
    | h1::t1, h2::t2 -> h1 `eq` h2 /\ t1 `list_equivalent eq` t2
    | _, _ -> False
  ))
let list_equivalent_destruct #a eq l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | h1::t1, h2::t2 -> (
    assert(h1 == List.Tot.index l1 0);
    assert(h2 == List.Tot.index l2 0);
    assert(forall i. List.Tot.index t1 i == List.Tot.index l1 (i+1));
    assert(forall i. List.Tot.index t2 i == List.Tot.index l2 (i+1))
  )

val list_equivalent_intro:
  #a:Type ->
  eq:equivalence a -> l1:list a -> l2:list a ->
  Lemma
  (requires (
    match l1, l2 with
    | [], [] -> True
    | h1::t1, h2::t2 -> h1 `eq` h2 /\ t1 `list_equivalent eq` t2
    | _, _ -> False
  ))
  (ensures l1 `list_equivalent eq` l2)
let list_equivalent_intro #a eq l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | h1::t1, h2::t2 -> (
    assert(forall i. List.Tot.index l1 i == (if i = 0 then h1 else List.Tot.index t1 (i-1)));
    assert(forall i. List.Tot.index l2 i == (if i = 0 then h2 else List.Tot.index t2 (i-1)))
  )

#push-options "--z3rlimit 25"
val mutual_auth_decompress_internal_list_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_cr:certificate_request_length_bounded bytes -> l1:list (handshake bytes) -> l2:list (handshake bytes) ->
  Lemma
  (requires l1 `list_equivalent handshake_equivalent` l2)
  (ensures (
    match mutual_auth_decompress_internal expected_cr l1, mutual_auth_decompress_internal expected_cr l2 with
    | Some decompressed_l1, Some decompressed_l2 -> decompressed_l1 `list_equivalent handshake_equivalent` decompressed_l2
    | _, _ -> True
  ))
let rec mutual_auth_decompress_internal_list_equivalent #bytes #bl expected_cr l1 l2 =
  match mutual_auth_decompress_internal expected_cr l1, mutual_auth_decompress_internal expected_cr l2 with
  | Some decompressed_l1, Some decompressed_l2 -> (
    list_equivalent_destruct handshake_equivalent l1 l2;
    match l1, l2 with
    | [], [] -> ()
    | h1_1::t1_1, h2_1::t2_1 -> (
      let h1_1: handshake bytes = h1_1 in
      let h2_1: handshake bytes = h2_1 in
      assert(h1_1.msg_type == h2_1.msg_type);
      if not (h1_1.msg_type = HT_encrypted_extensions) then (
        let Some new_t1_1 = mutual_auth_decompress_internal expected_cr t1_1 in
        let Some new_t2_1 = mutual_auth_decompress_internal expected_cr t2_1 in
        mutual_auth_decompress_internal_list_equivalent expected_cr t1_1 t2_1;
        list_equivalent_intro handshake_equivalent (h1_1::new_t1_1) (h2_1::new_t2_1)
      ) else (
        let expected_cr_length = length ((ps_prefix_to_ps_whole ps_certificate_request).serialize expected_cr) in
        let msg: handshake bytes = { msg_type = HT_certificate_request; length = expected_cr_length; msg = expected_cr; } in
        list_equivalent_destruct handshake_equivalent t1_1 t2_1;
        match t1_1, t2_1 with
        | [], [] -> ()
        | h1_2::t1_2, h2_2::t2_2 -> (
          let h1_2: handshake bytes = h1_2 in
          let h2_2: handshake bytes = h2_2 in
          if not (h1_2.msg_type = HT_certificate_request) then (
            list_equivalent_intro handshake_equivalent (msg::t1_1) (msg::t2_1);
            list_equivalent_intro handshake_equivalent (h1_1::msg::t1_1) (h2_1::msg::t2_1)
          ) else ()
        )
      )
    )
  )
  | _, _ -> ()
#pop-options

val mutual_auth_decompress_list_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  t:ctls_template bytes -> l1:list (handshake bytes) -> l2:list (handshake bytes) ->
  Lemma
  (requires l1 `list_equivalent handshake_equivalent` l2)
  (ensures (
    match mutual_auth_decompress t l1, mutual_auth_decompress t l2 with
    | Some decompressed_l1, Some decompressed_l2 -> decompressed_l1 `list_equivalent handshake_equivalent` decompressed_l2
    | _, _ -> True
  ))
let mutual_auth_decompress_list_equivalent #bytes #bl t l1 l2 =
  match get_mutual_auth_template t, get_signature_algorithm_template t with
  | Some mutual_auth, Some signature_algorithm -> (
    if mutual_auth = 0 then ()
    else (
      let expected_cr = mutual_auth_compute_cert_request signature_algorithm.signature_scheme in
      mutual_auth_decompress_internal_list_equivalent expected_cr l1 l2
    )
  )
  | _, _ -> ()

(*** Transcript modifications ***)

noeq
type modification_profile (bytes:Type0) {|bytes_like bytes|} =
  | NoModification: modification_profile bytes
  | HashClientHello1: (bytes -> tls_bytes bytes ({min = 0; max = (pow2 8)-1})) -> modification_profile bytes
  | CTLSCompress: ctls_template bytes -> modification_profile bytes

val dep_handshake: #bytes:Type0 -> {|bytes_like bytes|} -> ctls_unknowns bytes -> handshake bytes -> Type0
let dep_handshake #bytes #bl unk first_hs =
  if first_hs.msg_type = unk.ctls_template_handshake_type then
    match parse (ctls_template bytes) (first_hs.msg <: bytes) with
    | None -> handshake bytes
    | Some t -> ctls_transcript_handshake bytes unk t
  else
    handshake bytes

%splice [ps_dep_handshake] (gen_parser (`dep_handshake))

type modified_transcript (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) =
  first_hs:handshake bytes & list (dep_handshake unk first_hs)

val ps_modified_transcript: #bytes:Type0 -> {|bytes_like bytes|} -> unk:ctls_unknowns bytes -> parser_serializer_whole bytes (modified_transcript bytes unk)
let ps_modified_transcript #bytes #bl unk =
  mk_trivial_isomorphism_whole (bind_whole ps_handshake (fun first_hs -> ps_whole_list (ps_dep_handshake unk first_hs)))

val can_modify_transcript:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ctls_unknowns bytes ->
  modification_profile bytes -> tls_transcript bytes ->
  bool
let can_modify_transcript #bytes #bl unk p t =
  match t with
  | [] -> false
  | first_hs::_ -> (
    match p with
    | NoModification -> not (first_hs.msg_type = HT_message_hash || first_hs.msg_type = unk.ctls_template_handshake_type)
    | HashClientHello1 _ -> first_hs.msg_type = HT_client_hello
    | CTLSCompress template ->
      Some? (mutual_auth_compress template t) &&
      Some? ((list_compression (handshake_compression unk)).compress template (Some?.v (mutual_auth_compress template t))) &&
      length (serialize _ template <: bytes) < pow2 24
  )

val modify_transcript:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  p:modification_profile bytes -> t:tls_transcript bytes{can_modify_transcript unk p t} ->
  modified_transcript bytes unk
let modify_transcript #bytes #bl unk p t =
  match p with
  | NoModification -> (
    match t with
    | ht::tt -> (|ht, tt|)
  )
  | HashClientHello1 hash -> (
    match t with
    | ht::tt -> (
      let client_hello_1: client_hello bytes = ht.msg in
      let client_hello_1_bytes = (ps_prefix_to_ps_whole ps_client_hello).serialize ht.msg in
      let client_hello_1_hash = hash client_hello_1_bytes in
      let new_ht: handshake bytes = {
        msg_type = HT_message_hash;
        length = length #bytes client_hello_1_hash;
        msg = client_hello_1_hash;
      } in
      (|new_ht, tt|)
    )
  )
  | CTLSCompress template ->
    let Some compressed_t1 = mutual_auth_compress template t in
    let Some compressed_t2 = (list_compression (handshake_compression unk)).compress template compressed_t1 in
    let first_msg: bytes = serialize _ template in
    parse_serialize_inv_lemma #bytes _ template;
    let first_hs: handshake bytes = {
      msg_type = unk.ctls_template_handshake_type;
      length = length first_msg;
      msg = first_msg;
    } in
    (|first_hs, compressed_t2|)

val collision_condition:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  p1:modification_profile bytes -> p2:modification_profile bytes ->
  t1:tls_transcript bytes{can_modify_transcript unk p1 t1} -> t2:tls_transcript bytes{can_modify_transcript unk p2 t2} ->
  prop
let collision_condition #bytes #bl unk p1 p2 t1 t2 =
  match p1, p2 with
  // If both transcripts were modified by hashing ClientHello1,
  // then a hash collision can occur
  | HashClientHello1 hash1, HashClientHello1 hash2 -> (
    let ht1::_ = t1 in
    let ht2::_ = t2 in
    let buf1 = (ps_prefix_to_ps_whole ps_client_hello).serialize ht1.msg in
    let buf2 = (ps_prefix_to_ps_whole ps_client_hello).serialize ht2.msg in
    // The transcripts are equal
    t1 == t2 \/
    // Or we compute a hash collision
    (buf1 =!= buf2 /\ hash1 buf1 == hash2 buf2)
  )
  // If both transcripts were modified by cTLS compression,
  // then extensions of handshakes might be re-ordered
  | CTLSCompress temp1, CTLSCompress temp2 ->
    temp1 == temp2 /\
    list_equivalent handshake_equivalent t1 t2
  // Otherwise, the transcripts are equal
  | _, _ -> t1 == t2

val modify_transcript_injective:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  p1:modification_profile bytes -> p2:modification_profile bytes ->
  t1:tls_transcript bytes{can_modify_transcript unk p1 t1} -> t2:tls_transcript bytes{can_modify_transcript unk p2 t2} ->
  Lemma
  (requires modify_transcript unk p1 t1 == modify_transcript unk p2 t2)
  (ensures collision_condition unk p1 p2 t1 t2)
let modify_transcript_injective #bytes #bl unk p1 p2 t1 t2 =
  match p1, p2 with
  | NoModification, NoModification -> ()
  | HashClientHello1 hash1, HashClientHello1 hash2 -> (
    let ht1::_ = t1 in
    let ht2::_ = t2 in
    (ps_prefix_to_ps_whole #bytes ps_client_hello).parse_serialize_inv ht1.msg;
    (ps_prefix_to_ps_whole #bytes ps_client_hello).parse_serialize_inv ht2.msg
  )
  | CTLSCompress temp1, CTLSCompress temp2 -> (
    let Some compressed_t1_1 = mutual_auth_compress temp1 t1 in
    let Some compressed_t2_1 = mutual_auth_compress temp2 t2 in
    mutual_auth_decompress_compress temp1 t1;
    mutual_auth_decompress_compress temp2 t2;
    parse_serialize_inv_lemma #bytes (ctls_template bytes) temp1;
    parse_serialize_inv_lemma #bytes (ctls_template bytes) temp2;
    assert(temp1 == temp2);
    (list_compression (handshake_compression unk)).decompress_compress temp1 compressed_t1_1;
    (list_compression (handshake_compression unk)).decompress_compress temp2 compressed_t2_1;
    let Some compressed_t1_2 = (list_compression (handshake_compression unk)).compress temp1 compressed_t1_1 in
    let Some compressed_t2_2 = (list_compression (handshake_compression unk)).compress temp2 compressed_t2_1 in
    assert(compressed_t1_2 == compressed_t2_2);
    let Some t1_roundtrip = (list_compression (handshake_compression unk)).decompress temp1 compressed_t1_2 in
    let Some t2_roundtrip = (list_compression (handshake_compression unk)).decompress temp2 compressed_t2_2 in
    list_equivalent_symmetric handshake_equivalent handshake_equivalent_symmetric t1_roundtrip compressed_t1_1;
    list_equivalent_transitive handshake_equivalent handshake_equivalent_transitive compressed_t1_1 t1_roundtrip compressed_t2_1;
    mutual_auth_decompress_list_equivalent temp1 compressed_t1_1 compressed_t2_1
  )
  | _, _ -> ()
