module CTLS.Compressions

open FStar.List.Tot
open Comparse
open TLS13.MessageFormats
open TLS13.OldExtensions
open CTLS.Profile
open CTLS.MessageFormats

#set-options "--fuel 0 --ifuel 0"

(*** Compression types ***)

type equivalence (a:Type0) = eq:(a -> a -> prop){forall x. eq x x}

val equality_equivalence: #a:Type -> equivalence a
let equality_equivalence #a x y = x == y

noeq
type compression (bytes:Type0) {|bytes_like bytes|} (tls_type:Type0) (ctls_type: ctls_template bytes -> Type0) (tls_eq:equivalence tls_type) = {
  compress: t:ctls_template bytes -> x:tls_type -> option (ctls_type t);
  decompress: t:ctls_template bytes -> ctls_type t -> option tls_type;
  decompress_compress:
    t:ctls_template bytes -> x:tls_type ->
    Lemma (
      match compress t x with
      | None -> True
      | Some x_compressed -> (
        match decompress t x_compressed with
        | None -> False
        | Some x_roundtrip -> x_roundtrip `tls_eq` x
      )
    );
  compress_decompress:
    t:ctls_template bytes -> x_compressed:ctls_type t ->
    Lemma (
      match decompress t x_compressed with
      | None -> True
      | Some x_decompressed -> compress t x_decompressed == Some x_compressed
    );
}

unfold val (let?): #a:Type -> #b:Type -> x:option a -> (y:a -> Pure (option b) (requires Some y == x) (ensures fun _ -> True)) -> option b
unfold let (let?) #a #b x f =
  match x with
  | None -> None
  | Some y -> f y

val no_compression: #bytes:Type0 -> {|bytes_like bytes|} -> a:Type0 -> compression bytes a (no_template_dep a) equality_equivalence
let no_compression #bytes #bl a = {
  compress = (fun t x -> Some x);
  decompress = (fun t x -> Some x);
  decompress_compress = (fun t x -> ());
  compress_decompress = (fun t x -> ());
}

val compression_to_bytes:
  bytes:Type0 -> {|bytes_like bytes|} ->
  tls_type:Type0 -> parser_serializer_whole bytes tls_type ->
  ctls_type:(ctls_template bytes -> Type0) ->
  compression bytes tls_type ctls_type equality_equivalence ->
  compression bytes bytes ctls_type equality_equivalence
let compression_to_bytes bytes #bl tls_type ps_tls_type ctls_type comp =
  {
    compress = (fun t b ->
      let? x = ps_tls_type.parse b in
      comp.compress t x
    );
    decompress = (fun t x ->
      let? x_decompressed = comp.decompress t x in
      Some (ps_tls_type.serialize x_decompressed)
    );
    decompress_compress = (fun t b ->
      match ps_tls_type.parse b with
      | None -> ()
      | Some x -> (
        comp.decompress_compress t x;
        ps_tls_type.serialize_parse_inv b
      )
    );
    compress_decompress = (fun t x ->
      match comp.decompress t x with
      | None -> ()
      | Some x_decompressed -> (
        ps_tls_type.parse_serialize_inv x_decompressed;
        comp.compress_decompress t x
      )
    );
  }

val mk_compression:
  #a:Type0 -> #bytes:Type0 -> {|bytes_like bytes|} ->
  #get_template_elem:(ctls_template bytes -> option a) ->
  #default_ty:Type0 -> #parametric_ty:(a -> Type0) ->
  #eq:equivalence default_ty ->
  compress:(t:a -> default_ty -> option (parametric_ty t)) ->
  decompress:(t:a -> parametric_ty t -> option default_ty) ->
  decompress_compress:(t:a -> x:default_ty -> Lemma (
      match compress t x with
      | None -> True
      | Some x_compressed -> (
        match decompress t x_compressed with
        | None -> False
        | Some x_roundtrip -> x_roundtrip `eq` x
      )
)) ->
  compress_decompress:(t:a -> x_compressed:parametric_ty t -> Lemma (
      match decompress t x_compressed with
      | None -> True
      | Some x_decompressed -> compress t x_decompressed == Some x_compressed
)) ->
  compression bytes default_ty (mk_templated_type bytes get_template_elem default_ty parametric_ty) eq
let mk_compression #a #bytes #bl #get_template_elem #default_ty #parametric_ty #eq compress decompress decompress_compress compress_decompress =
  let compress (template:ctls_template bytes) (x:default_ty): option (mk_templated_type bytes get_template_elem default_ty parametric_ty template) =
    match get_template_elem template with
    | None -> Some x
    | Some param -> compress param x
  in
  let decompress (template:ctls_template bytes) (y:mk_templated_type bytes get_template_elem default_ty parametric_ty template): option default_ty =
    match get_template_elem template with
    | None -> Some y
    | Some param -> decompress param y
  in
  {
    compress;
    decompress;
    decompress_compress = (fun template x ->
      match get_template_elem template with
      | None -> ()
      | Some param -> decompress_compress param x
    );
    compress_decompress = (fun template (y:mk_templated_type bytes get_template_elem default_ty parametric_ty template) ->
      match get_template_elem template with
      | None -> ()
      | Some param -> compress_decompress param y
    );
  }

(*** Helper: list compression ***)

val list_ctls_type:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  (ctls_template bytes -> Type0) ->
  (ctls_template bytes -> Type0)
let list_ctls_type #bytes #bl c = fun t ->
  list (c t)

val list_equivalent:
  #a:Type ->
  equivalence a ->
  equivalence (list a)
let list_equivalent #a eq = fun l1 l2 ->
  List.Tot.length l1 = List.Tot.length l2 /\
  (forall i. (List.Tot.index l1 i) `eq` (List.Tot.index l2 i))

val list_equivalent_symmetric:
  #a:Type ->
  eq:equivalence a ->
  eq_sym:(
    x1:a -> x2:a ->
    Lemma
    (requires x1 `eq` x2)
    (ensures x2 `eq` x1)
  ) ->
  l1:list a -> l2:list a ->
  Lemma
  (requires l1 `list_equivalent eq` l2)
  (ensures l2 `list_equivalent eq` l1)
let list_equivalent_symmetric #a eq eq_sym l1 l2 =
  introduce forall i. (List.Tot.index l2 i) `eq` (List.Tot.index l1 i) with (
    eq_sym (List.Tot.index l1 i) (List.Tot.index l2 i)
  )

val list_equivalent_transitive:
  #a:Type ->
  eq:equivalence a ->
  eq_trans:(
    x1:a -> x2:a -> x3:a ->
    Lemma
    (requires x1 `eq` x2 /\ x2 `eq` x3)
    (ensures x1 `eq` x3)
  ) ->
  l1:list a -> l2:list a -> l3:list a ->
  Lemma
  (requires l1 `list_equivalent eq` l2 /\ l2 `list_equivalent eq` l3)
  (ensures l1 `list_equivalent eq` l3)
let list_equivalent_transitive #a eq eq_trans l1 l2 l3 =
  introduce forall i. (List.Tot.index l1 i) `eq` (List.Tot.index l3 i) with (
    eq_trans (List.Tot.index l1 i) (List.Tot.index l2 i) (List.Tot.index l3 i)
  )

#push-options "--ifuel 1"
val mapM:
  #a:Type -> #b:Type ->
  (a -> option b) -> list a ->
  option (list b)
let rec mapM #a #b f l =
  match l with
  | [] -> Some []
  | h::t ->
    let? fh = f h in
    let? ft = mapM f t in
    Some (fh::ft)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val list_equivalent_cons:
  #a:Type ->
  eq:equivalence a ->
  h1:a -> t1:list a ->
  h2:a -> t2:list a ->
  Lemma
  (requires (h1 `eq` h2) /\ (t1 `list_equivalent eq` t2))
  (ensures ((h1::t1) `list_equivalent eq` (h2::t2)))
let list_equivalent_cons #a eq h1 t1 h2 t2 =
  introduce forall i. (List.Tot.index (h1::t1) i) `eq` (List.Tot.index (h2::t2) i) with (
    if i = 0 then ()
    else (
      // Trigger the forall with (i-1) with the correct type
      let _ = List.Tot.index t1 (i-1) in
      ()
    )
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val mapM_roundtrip:
  #a:Type -> #b:Type ->
  f:(a -> option b) -> g:(b -> option a) ->
  l:list a ->
  eq:equivalence a ->
  f_g_eq:(x:a -> Lemma (
    match f x with
    | None -> True
    | Some fx ->
      match g fx with
      | None -> False
      | Some gfx ->
        gfx `eq` x
  )) ->
  Lemma (
    match mapM f l with
    | None -> True
    | Some fl ->
      match mapM g fl with
      | None -> False
      | Some gfl ->
        gfl `list_equivalent eq` l
  )
let rec mapM_roundtrip #a #b f g l eq f_g_eq =
  match l with
  | [] -> ()
  | h::t -> (
    f_g_eq h;
    mapM_roundtrip f g t eq f_g_eq;
    match f h, mapM f t with
    | Some fh, Some ft -> (
      let Some gfh = g fh in
      let Some gft = mapM g ft in
      list_equivalent_cons eq gfh gft h t
    )
    | _, _ -> ()
  )
#pop-options

#push-options "--ifuel 1 --fuel 0"
val list_compression:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tls_type:Type0 -> #ctls_type:(ctls_template bytes -> Type0) -> #tls_eq:equivalence tls_type ->
  compression bytes tls_type ctls_type tls_eq ->
  compression bytes (list tls_type) (list_ctls_type ctls_type) (list_equivalent tls_eq)
let list_compression #bytes #bl #tls_type #ctls_type #tls_eq comp = {
  compress = (fun (t:ctls_template bytes) (x:list tls_type) ->
    mapM (comp.compress t) x
  );
  decompress = (fun (t:ctls_template bytes) (x:list_ctls_type ctls_type t) ->
    mapM (comp.decompress t) x
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:list tls_type) ->
    mapM_roundtrip (comp.compress t) (comp.decompress t) x tls_eq (comp.decompress_compress t)
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:list_ctls_type ctls_type t) ->
    mapM_roundtrip (comp.decompress t) (comp.compress t) x equality_equivalence (comp.compress_decompress t);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (List.Tot.index_extensionality x))
  );
}
#pop-options

(*** Ciphersuite ***)

#push-options "--fuel 2 --ifuel 2"
val cipher_suites_compression:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  compression bytes (tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2})) (ctls_cipher_suites bytes) equality_equivalence
let cipher_suites_compression #bytes #bl =
  let compress (param:ctls_cipher_suite_template bytes) (x:tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2})): option (pre_ctls_cipher_suites bytes param) =
    if x = [param] then
      Some ()
    else
      None
  in
  let decompress (param:ctls_cipher_suite_template bytes) (y:pre_ctls_cipher_suites bytes param): option (tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2})) =
    Some ([param])
  in
  mk_compression compress decompress
    (fun param (x:tls_list bytes (ps_cipher_suite) ({min=2; max=(pow2 16)-2})) -> ())
    (fun param (y:pre_ctls_cipher_suites bytes param) -> ())
#pop-options

val cipher_suite_compression:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  compression bytes (cipher_suite) (ctls_cipher_suite bytes) equality_equivalence
let cipher_suite_compression #bytes #bl =
  let compress (param:ctls_cipher_suite_template bytes) (x:cipher_suite): option (pre_ctls_cipher_suite bytes param) =
    if x = param then
      Some ()
    else
      None
  in
  let decompress (param:ctls_cipher_suite_template bytes) (y:pre_ctls_cipher_suite bytes param): option (cipher_suite) =
    Some (param)
  in
  mk_compression compress decompress
    (fun param (x:cipher_suite) -> ())
    (fun param (y:pre_ctls_cipher_suite bytes param) -> ())

(*** DH group ***)

#push-options "--fuel 2 --ifuel 2"
val key_share_client_hello_compression: #bytes:Type0 -> {|bytes_like bytes|} -> compression bytes (key_share_client_hello bytes) (ctls_key_share_client_hello bytes) equality_equivalence
let key_share_client_hello_compression #bytes #bl =
  let compress (param:ctls_dh_group_template bytes) (x:key_share_client_hello bytes): option (pre_ctls_key_share_client_hello bytes param) =
    match x.client_shares with
    | [key_share] -> (
      if (
        key_share.group = param.group_name &&
        (param.key_share_length = 0 || length #bytes key_share.key_exchange = param.key_share_length)
      ) then (
        Some ({ client_shares = key_share.key_exchange; })
      ) else None
    )
    | _ -> None
  in
  let decompress (param:ctls_dh_group_template bytes) (y:pre_ctls_key_share_client_hello bytes param): option (key_share_client_hello bytes) =
    let client_share = {
      group = param.group_name;
      key_exchange = y.client_shares;
    } in
    if length #bytes y.client_shares < pow2 16 - 4 then (
      Some ({
        client_shares = [client_share];
      } <: key_share_client_hello bytes)
    ) else None
  in
  mk_compression compress decompress
    (fun param (x:key_share_client_hello bytes) -> ())
    (fun param (y:pre_ctls_key_share_client_hello bytes param) -> ())
#pop-options

val key_share_server_hello_compression: #bytes:Type0 -> {|bytes_like bytes|} -> compression bytes (key_share_server_hello bytes) (ctls_key_share_server_hello bytes) equality_equivalence
let key_share_server_hello_compression #bytes #bl =
  let compress (param:ctls_dh_group_template bytes) (x:key_share_server_hello bytes): option (pre_ctls_key_share_server_hello bytes param) =
    let key_share = x.server_share in
    if (
      key_share.group = param.group_name &&
      (param.key_share_length = 0 || length #bytes key_share.key_exchange = param.key_share_length)
    ) then (
      Some { server_share = x.server_share.key_exchange; }
    ) else None
  in
  let decompress (param:ctls_dh_group_template bytes) (y:pre_ctls_key_share_server_hello bytes param): option (key_share_server_hello bytes) =
    Some ({
      server_share = {
        group = param.group_name;
        key_exchange = y.server_share;
      }
    } <: key_share_server_hello bytes)
  in
  mk_compression compress decompress
    (fun param (x:key_share_server_hello bytes) -> ())
    (fun param (y:pre_ctls_key_share_server_hello bytes param) -> ())

(*** Signature algorithm ***)

val certificate_verify_algorithm_compression: #bytes:Type0 -> {|bytes_like bytes|} -> compression bytes signature_scheme (ctls_certificate_verify_algorithm bytes) equality_equivalence
let certificate_verify_algorithm_compression #bytes #bl =
  let compress (param:ctls_signature_algorithm_template bytes) (x:signature_scheme): option (pre_ctls_certificate_verify_algorithm bytes param) =
    if x = param.signature_scheme then
      Some ()
    else
      None
  in
  let decompress (param:ctls_signature_algorithm_template bytes) (y:pre_ctls_certificate_verify_algorithm bytes param): option signature_scheme =
    Some param.signature_scheme
  in
  mk_compression compress decompress
    (fun param (x:signature_scheme) -> ())
    (fun param (y:pre_ctls_certificate_verify_algorithm bytes param) -> ())

val certificate_verify_signature_compression: #bytes:Type0 -> {|bytes_like bytes|} -> compression bytes (tls_bytes bytes (({min=0; max=(pow2 16)-1}))) (ctls_certificate_verify_signature bytes) equality_equivalence
let certificate_verify_signature_compression #bytes #bl =
  let compress (param:ctls_signature_algorithm_template bytes) (x:tls_bytes bytes (({min=0; max=(pow2 16)-1}))): option (pre_ctls_certificate_verify_signature bytes param) =
    if param.signature_length = 0 || length (x <: bytes) = param.signature_length then
      Some x
    else
      None
  in
  let decompress (param:ctls_signature_algorithm_template bytes) (y:pre_ctls_certificate_verify_signature bytes param): option (tls_bytes bytes (({min=0; max=(pow2 16)-1}))) =
    Some y
  in
  mk_compression compress decompress
    (fun param (x:tls_bytes bytes (({min=0; max=(pow2 16)-1}))) -> ())
    (fun param (y:pre_ctls_certificate_verify_signature bytes param) -> ())

(*** Random ***)

val random_compression: #bytes:Type0 -> {|bytes_like bytes|} -> compression bytes (random bytes) (ctls_random bytes) equality_equivalence
let random_compression #bytes #bl =
  let compress (sz:ctls_random_template bytes) (x:random bytes): option (pre_ctls_random bytes sz) =
    let? (lhs, rhs) = split #bytes x sz in
    if to_nat rhs = Some 0 then
      Some (lhs <: pre_ctls_random bytes sz)
    else None
  in
  let decompress (sz:ctls_random_template bytes) (x:pre_ctls_random bytes sz): option (random bytes) =
    Some (concat #bytes x (from_nat (32 - sz) 0))
  in
  mk_compression compress decompress
    (fun (sz:ctls_random_template bytes) (x:random bytes) ->
      concat_split #bytes x sz;
      match split #bytes x sz with
      | Some (lhs, rhs) -> to_from_nat #bytes rhs
      | None -> ()
    )
    (fun (sz:ctls_random_template bytes) (y:pre_ctls_random bytes sz) ->
      from_to_nat #bytes (32 - sz) 0;
      split_concat #bytes y (from_nat (32 - sz) 0)
    )

(*** Extension: framework ***)

val extensions_eq: #bytes:eqtype -> {|bytes_like bytes|} -> equivalence (list (extension bytes))
let extensions_eq #bytes #bl = fun l1 l2 ->
  forall (x:extension bytes). List.Tot.count x l1 == List.Tot.count x l2

// Stage 1 : predefined extensions

// Stage 1.1: one predefined extensions

#push-options "--ifuel 1 --fuel 1"
val extensions_one_predefined_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  extension bytes -> list (extension bytes) ->
  option (list (extension bytes))
let rec extensions_one_predefined_compress #bytes #bl predefined_ext exts =
  match exts with
  | [] -> None
  | h::t ->
    if h = predefined_ext then
      Some t
    else (
      let? compressed_t = extensions_one_predefined_compress predefined_ext t in
      Some (h::compressed_t)
    )
#pop-options

val extensions_one_predefined_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_ext:extension bytes ->
  compressed_exts:list (extension bytes) ->
  list (extension bytes)
let extensions_one_predefined_decompress #bytes #bl predefined_ext compressed_exts =
  predefined_ext::compressed_exts

#push-options "--ifuel 2 --fuel 2"
val extensions_one_predefined_decompress_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_ext:extension bytes -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_one_predefined_compress predefined_ext exts))
  (ensures extensions_one_predefined_decompress predefined_ext (Some?.v (extensions_one_predefined_compress predefined_ext exts)) `extensions_eq` exts)
let rec extensions_one_predefined_decompress_compress #bytes #bl predefined_ext exts =
  match exts with
  | h::t ->
    if h = predefined_ext then ()
    else extensions_one_predefined_decompress_compress predefined_ext t
#pop-options

#push-options "--ifuel 1 --fuel 1"
val count_extensions_one_predefined_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_ext:extension bytes -> exts:list (extension bytes) ->
  ext:extension bytes ->
  Lemma
  (requires Some? (extensions_one_predefined_compress predefined_ext exts))
  (ensures (List.Tot.count ext exts == ((if ext = predefined_ext then 1 else 0) +  List.Tot.count ext (Some?.v (extensions_one_predefined_compress predefined_ext exts)))))
let rec count_extensions_one_predefined_compress #bytes #bl predefined_ext exts ext =
  match exts with
  | h::t ->
    if h = predefined_ext then ()
    else (
      count_extensions_one_predefined_compress predefined_ext t ext
    )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_one_predefined_decompress_compress_eq:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_ext:extension bytes -> exts:list (extension bytes) -> compressed_exts:list (extension bytes) ->
  Lemma
  (requires
    Some? (extensions_one_predefined_compress predefined_ext exts) /\
    (Some?.v (extensions_one_predefined_compress predefined_ext exts)) `extensions_eq` compressed_exts
  )
  (ensures extensions_one_predefined_decompress predefined_ext compressed_exts `extensions_eq` exts)
let extensions_one_predefined_decompress_compress_eq #bytes #bl predefined_ext exts compressed_exts =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (count_extensions_one_predefined_compress predefined_ext exts))
#pop-options

#push-options "--ifuel 0 --fuel 1"
val extensions_one_predefined_compress_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_ext:extension bytes -> compressed_exts:list (extension bytes) ->
  Lemma (
    Some? (extensions_one_predefined_compress predefined_ext (extensions_one_predefined_decompress predefined_ext compressed_exts)) /\
    Some?.v (extensions_one_predefined_compress predefined_ext (extensions_one_predefined_decompress predefined_ext compressed_exts)) == compressed_exts
  )
let extensions_one_predefined_compress_decompress #bytes #bl predefined_ext compressed_exts = ()
#pop-options

// Stage 1.2: several predefined extensions

#push-options "--ifuel 1 --fuel 1"
val extensions_predefined_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  list (extension bytes) -> list (extension bytes) ->
  option (list (extension bytes))
let rec extensions_predefined_compress #bytes #bl predefined_exts exts =
  match predefined_exts with
  | [] -> Some exts
  | h_pe::t_pe ->
    let? exts_compressed = (extensions_one_predefined_compress h_pe exts) in
    extensions_predefined_compress t_pe exts_compressed
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_predefined_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_exts:list (extension bytes) ->
  compressed_exts:list (extension bytes) ->
  list (extension bytes)
let rec extensions_predefined_decompress #bytes #bl predefined_exts compressed_exts =
  match predefined_exts with
  | [] -> compressed_exts
  | h_pe::t_pe ->
    extensions_one_predefined_decompress h_pe (extensions_predefined_decompress t_pe compressed_exts)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_predefined_decompress_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_exts:list (extension bytes) -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_predefined_compress predefined_exts exts))
  (ensures extensions_predefined_decompress predefined_exts (Some?.v (extensions_predefined_compress predefined_exts exts)) `extensions_eq` exts)
let rec extensions_predefined_decompress_compress #bytes #bl predefined_exts exts =
  match predefined_exts with
  | [] -> ()
  | h_pe::t_pe ->
    extensions_one_predefined_decompress_compress h_pe exts;
    match extensions_one_predefined_compress h_pe exts with
    | None -> ()
    | Some exts_compressed -> (
      extensions_predefined_decompress_compress t_pe exts_compressed
    )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_predefined_decompress_compress_eq:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_exts:list (extension bytes) -> exts:list (extension bytes) -> compressed_exts:list (extension bytes) ->
  Lemma
  (requires
    Some? (extensions_predefined_compress predefined_exts exts) /\
    (Some?.v (extensions_predefined_compress predefined_exts exts)) `extensions_eq` compressed_exts
  )
  (ensures extensions_predefined_decompress predefined_exts compressed_exts `extensions_eq` exts)
let rec extensions_predefined_decompress_compress_eq #bytes #bl predefined_exts exts compressed_exts =
  match predefined_exts with
  | [] -> ()
  | h_pe::t_pe ->
    let Some exts_compressed = extensions_one_predefined_compress h_pe exts  in
    extensions_predefined_decompress_compress_eq t_pe exts_compressed compressed_exts;
    extensions_one_predefined_decompress_compress_eq h_pe exts (extensions_predefined_decompress t_pe compressed_exts)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_predefined_compress_decompress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  predefined_exts:list (extension bytes) -> compressed_exts:list (extension bytes) ->
  Lemma (
    Some? (extensions_predefined_compress predefined_exts (extensions_predefined_decompress predefined_exts compressed_exts)) /\
    Some?.v (extensions_predefined_compress predefined_exts (extensions_predefined_decompress predefined_exts compressed_exts)) == compressed_exts
  )
let rec extensions_predefined_compress_decompress #bytes #bl predefined_exts compressed_exts =
  match predefined_exts with
  | [] -> ()
  | h_pe::t_pe ->
    extensions_one_predefined_compress_decompress h_pe (extensions_predefined_decompress t_pe compressed_exts);
    extensions_predefined_compress_decompress t_pe compressed_exts
#pop-options

// Stage 2 : expected extensions

// Stage 2.1 : one expected extensions

#push-options "--ifuel 1 --fuel 1"
val extensions_one_expected_compress:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_type -> list (extension bytes) ->
  option (extension bytes & list (extension bytes))
let rec extensions_one_expected_compress #bytes #bl expected_ty exts =
  match exts with
  | [] -> None
  | h_ext::t_ext ->
    if h_ext.extension_type = expected_ty then
      Some (h_ext, t_ext)
    else (
      let? (res_ext, res_exts) = extensions_one_expected_compress expected_ty t_ext in
      Some (res_ext, h_ext::res_exts)
    )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_one_expected_decompress:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  expected_ext:extension bytes -> compressed_exts:list (extension bytes) ->
  list (extension bytes)
let extensions_one_expected_decompress expected_ext compressed_exts =
  expected_ext::compressed_exts
#pop-options

#push-options "--ifuel 2 --fuel 1"
val count_extensions_one_expected_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_ty:extension_type -> exts:list (extension bytes) ->
  ext:extension bytes ->
  Lemma
  (requires Some? (extensions_one_expected_compress expected_ty exts))
  (ensures (
    let Some (expected_ext, compressed_exts) = extensions_one_expected_compress expected_ty exts in
    List.Tot.count ext exts == (if ext = expected_ext then 1 else 0) + List.Tot.count ext compressed_exts
  ))
let rec count_extensions_one_expected_compress #bytes #bl expected_ty exts ext =
  match exts with
  | [] -> assert(False)
  | h_ext::t_ext ->
    if h_ext.extension_type = expected_ty then ()
    else (
      count_extensions_one_expected_compress expected_ty t_ext ext
    )
#pop-options

#push-options "--ifuel 2 --fuel 1"
val extensions_one_expected_decompress_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_ty:extension_type -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_one_expected_compress expected_ty exts))
  (ensures (
    let Some (expected_ext, compressed_exts) = extensions_one_expected_compress expected_ty exts in
    extensions_one_expected_decompress expected_ext compressed_exts `extensions_eq` exts
  ))
let extensions_one_expected_decompress_compress #bytes #bl expected_ty exts =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (count_extensions_one_expected_compress expected_ty exts))
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_one_expected_compress_correct:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  expected_ty:extension_type -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_one_expected_compress expected_ty exts))
  (ensures (
    let Some (expected_ext, _) = extensions_one_expected_compress expected_ty exts in
    expected_ext.extension_type == expected_ty
  ))
let rec extensions_one_expected_compress_correct #bytes #bl expected_ty exts =
  match exts with
  | [] -> assert(False)
  | h_ext::t_ext ->
    if h_ext.extension_type = expected_ty then ()
    else (
      extensions_one_expected_compress_correct expected_ty t_ext
    )
#pop-options

// Stage 2.2 : several expected extensions

val get_extensions_types: #bytes:Type0 -> {|bytes_like bytes|} -> list (extension bytes) -> list extension_type
let get_extensions_types #bytes #bl exts = (List.Tot.map Mkextension?.extension_type exts)

#push-options "--ifuel 1 --fuel 1"
val extensions_expected_compress:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list extension_type -> list (extension bytes) ->
  option (list (extension bytes) & list (extension bytes))
let rec extensions_expected_compress #bytes #bl expected_tys exts =
  match expected_tys with
  | [] -> Some ([], exts)
  | h_expected_ty::t_expected_ty -> (
    let? (expected_h_ext, other_exts) = extensions_one_expected_compress h_expected_ty exts in
    let? (expected_t_ext, other_exts) = extensions_expected_compress t_expected_ty other_exts in
    Some (expected_h_ext::expected_t_ext, other_exts)
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_expected_decompress:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  expected_exts:list (extension bytes) -> other_exts:list (extension bytes) ->
  list (extension bytes)
let rec extensions_expected_decompress #bytes #bl expected_exts other_exts =
  match expected_exts with
  | [] -> other_exts
  | h_expected_exts::t_expected_exts ->
    extensions_one_expected_decompress h_expected_exts (extensions_expected_decompress t_expected_exts other_exts)
#pop-options

#push-options "--ifuel 2 --fuel 1"
val extensions_expected_decompress_compress:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  expected_tys:list extension_type -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_expected_compress expected_tys exts))
  (ensures (
    let Some (expected_exts, other_exts) = (extensions_expected_compress expected_tys exts) in
    extensions_expected_decompress expected_exts other_exts `extensions_eq` exts
  ))
let rec extensions_expected_decompress_compress #bytes #bl expected_tys exts =
  match expected_tys with
  | [] -> ()
  | h_expected_ty::t_expected_ty -> (
    let Some (expected_h_ext, other_exts) = extensions_one_expected_compress h_expected_ty exts in
    extensions_one_expected_decompress_compress h_expected_ty exts;
    extensions_expected_decompress_compress t_expected_ty other_exts
  )
#pop-options

#push-options "--ifuel 2 --fuel 1"
val extensions_expected_compress_correct:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  expected_tys:list extension_type -> exts:list (extension bytes) ->
  Lemma
  (requires Some? (extensions_expected_compress expected_tys exts))
  (ensures (
    let Some (expected_exts, _) = extensions_expected_compress expected_tys exts in
    List.Tot.length expected_exts == List.Tot.length expected_tys /\
    expected_tys == get_extensions_types expected_exts
  ))
let rec extensions_expected_compress_correct #bytes #bl expected_tys exts =
  match expected_tys with
  | [] -> ()
  | h_expected_ty::t_expected_ty -> (
    let Some (expected_h_ext, other_exts) = extensions_one_expected_compress h_expected_ty exts in
    extensions_one_expected_compress_correct h_expected_ty exts;
    extensions_expected_compress_correct t_expected_ty other_exts
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val extensions_expected_compress_decompress:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  expected_exts:list (extension bytes) -> compressed_exts:list (extension bytes) ->
  Lemma (extensions_expected_compress (get_extensions_types expected_exts) (extensions_expected_decompress expected_exts compressed_exts) == Some (expected_exts, compressed_exts))
let rec extensions_expected_compress_decompress #bytes #bl expected_exts compressed_exts =
  match expected_exts with
  | [] -> ()
  | h_expected_exts::t_expected_exts -> (
    extensions_expected_compress_decompress t_expected_exts compressed_exts
  )
#pop-options

// Stage 3: finalize everything

noeq type ctls_extensions_comp (bytes:Type0) {|bytes_like bytes|} = {
  tys: ctls_extensions_types bytes;
  expected_comp: ext_ty:extension_type -> compression bytes (tls_extension_inner bytes) (tys.expected_ty ext_ty).typ equality_equivalence;
  additional_comp: ext_ty:extension_type -> compression bytes (tls_extension_inner bytes) (tys.additional_ty ext_ty).typ equality_equivalence;
}


#push-options "--ifuel 1 --fuel 1"
val compress_expected_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  exts:list (extension bytes) ->
  option (ctls_expected_extensions ext_comp.tys temp (get_extensions_types exts))
let rec compress_expected_extensions #bytes #bl ext_comp temp exts =
  match exts with
  | [] -> Some ()
  | h::t -> (
    let? h_compressed = (ext_comp.expected_comp h.extension_type).compress temp {extension_data = h.extension_data} in
    let? t_compressed = compress_expected_extensions ext_comp temp t in
    Some (h_compressed, t_compressed)
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val decompress_expected_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  ext_tys:list extension_type ->
  ctls_expected_extensions ext_comp.tys temp ext_tys ->
  option (exts:list (extension bytes){get_extensions_types exts == ext_tys})
let rec decompress_expected_extensions #bytes #bl ext_comp temp ext_tys compressed_exts =
  match ext_tys with
  | [] -> Some []
  | ext_ty_h::ext_ty_t -> (
    let (compressed_ext_h, compressed_ext_t): ctls_expected_extensions ext_comp.tys temp (ext_ty_h::ext_ty_t) = compressed_exts in
    let? h_data_decompressed = (ext_comp.expected_comp ext_ty_h).decompress temp compressed_ext_h in
    let h_decompressed: extension bytes = {
      extension_type = ext_ty_h;
      extension_data = h_data_decompressed.extension_data;
    } in
    let? t_decompressed = decompress_expected_extensions ext_comp temp ext_ty_t compressed_ext_t in
    Some (h_decompressed::t_decompressed <: exts:list (extension bytes){get_extensions_types exts == ext_tys})
  )
#pop-options

#push-options "--ifuel 3 --fuel 3"
val decompress_compress_expected_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  exts:list (extension bytes) ->
  Lemma
  (requires Some? (compress_expected_extensions ext_comp temp exts))
  (ensures decompress_expected_extensions ext_comp temp (get_extensions_types exts) (Some?.v (compress_expected_extensions ext_comp temp exts)) == Some exts)
let rec decompress_compress_expected_extensions #bytes #bl ext_comp temp exts =
  match exts with
  | [] -> (
    assert(decompress_expected_extensions ext_comp temp (get_extensions_types exts) (Some?.v (compress_expected_extensions ext_comp temp exts)) == Some [])
  )
  | ext_h::ext_t -> (
    (ext_comp.expected_comp ext_h.extension_type).decompress_compress temp {extension_data = ext_h.extension_data};
    decompress_compress_expected_extensions ext_comp temp ext_t;
    assert(decompress_expected_extensions ext_comp temp (get_extensions_types exts) (Some?.v (compress_expected_extensions ext_comp temp exts)) == Some exts)
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val compress_decompress_expected_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  ext_tys:list extension_type ->
  compressed_exts:ctls_expected_extensions ext_comp.tys temp ext_tys ->
  Lemma
  (requires Some? (decompress_expected_extensions ext_comp temp ext_tys compressed_exts))
  (ensures compress_expected_extensions ext_comp temp (Some?.v (decompress_expected_extensions ext_comp temp ext_tys compressed_exts)) == Some compressed_exts)
let rec compress_decompress_expected_extensions #bytes #bl ext_comp temp ext_tys compressed_exts =
  match ext_tys with
  | [] -> ()
  | h_ety::t_ety -> (
    let (h_ce, t_ce): ctls_expected_extensions ext_comp.tys temp (h_ety::t_ety) = compressed_exts in
    (ext_comp.expected_comp h_ety).compress_decompress temp h_ce;
    compress_decompress_expected_extensions ext_comp temp t_ety t_ce
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val compress_additional_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  exts:list (extension bytes) ->
  option (list (compressed_extension bytes ext_comp.tys temp))
let rec compress_additional_extensions #bytes #bl ext_comp temp exts =
  match exts with
  | [] -> Some []
  | h::t -> (
    let? h_compressed = (ext_comp.additional_comp h.extension_type).compress temp {extension_data = h.extension_data} in
    let? t_compressed = compress_additional_extensions ext_comp temp t in
    Some (({
      extension_type = h.extension_type;
      extension_data = h_compressed;
    } <: compressed_extension bytes ext_comp.tys temp)::t_compressed)
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val decompress_additional_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  list (compressed_extension bytes ext_comp.tys temp) ->
  option (list (extension bytes))
let rec decompress_additional_extensions #bytes #bl ext_comp temp compressed_exts =
  match compressed_exts with
  | [] -> Some []
  | h::t -> (
    let? h_decompressed = (ext_comp.additional_comp h.extension_type).decompress temp h.extension_data in
    let? t_decompressed = decompress_additional_extensions ext_comp temp t in
    Some (({
      extension_type = h.extension_type;
      extension_data = h_decompressed.extension_data;
    } <: extension bytes)::t_decompressed)
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val decompress_compress_additional_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  exts:list (extension bytes) ->
  Lemma
  (requires Some? (compress_additional_extensions ext_comp temp exts))
  (ensures decompress_additional_extensions ext_comp temp (Some?.v (compress_additional_extensions ext_comp temp exts)) == Some exts)
let rec decompress_compress_additional_extensions #bytes #bl ext_comp temp exts =
  match exts with
  | [] -> ()
  | ext_h::ext_t -> (
    (ext_comp.additional_comp ext_h.extension_type).decompress_compress temp {extension_data = ext_h.extension_data};
    decompress_compress_additional_extensions ext_comp temp ext_t
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val compress_decompress_additional_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> temp:ctls_template bytes ->
  compressed_exts:list (compressed_extension bytes ext_comp.tys temp) ->
  Lemma
  (requires Some? (decompress_additional_extensions ext_comp temp compressed_exts))
  (ensures compress_additional_extensions ext_comp temp (Some?.v (decompress_additional_extensions ext_comp temp compressed_exts)) == Some compressed_exts)
let rec compress_decompress_additional_extensions #bytes #bl ext_comp temp compressed_exts =
  match compressed_exts with
  | [] -> ()
  | h::t -> (
    (ext_comp.additional_comp h.extension_type).compress_decompress temp h.extension_data;
    compress_decompress_additional_extensions ext_comp temp t
  )
#pop-options

#push-options "--ifuel 2 --fuel 1"
val extensions_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ext_comp:ctls_extensions_comp bytes -> get_ext_temp:(ctls_template bytes -> ctls_extensions_template bytes) ->
  compression bytes (list (extension bytes)) (extensions_ctls_type ext_comp.tys get_ext_temp) extensions_eq
let extensions_compression #bytes #bl ext_comp get_ext_temp =
  let compress (temp:ctls_template bytes) (exts:list (extension bytes)): option (extensions_ctls_type ext_comp.tys get_ext_temp temp) =
    let ext_temp = get_ext_temp temp in
    let? exts_to_define = extensions_predefined_compress ext_temp.predefined_extensions exts in
    let? (exts_expected, exts_additional) = extensions_expected_compress ext_temp.expected_extensions exts_to_define in
    let? exts_expected_compressed = compress_expected_extensions ext_comp temp exts_expected in
    let? exts_additional_compressed = compress_additional_extensions ext_comp temp exts_additional in
    extensions_expected_compress_correct ext_temp.expected_extensions exts_to_define;
    if ext_temp.allow_additional then (
      let content: ctls_extensions_allow_additional_internal _ _ _ _ = ({
          expected_extensions = exts_expected_compressed;
          additional_extensions = exts_additional_compressed;
      }) in
      let content_length = length ((ps_whole_ctls_extensions_allow_additional_internal ext_comp.tys ext_temp.expected_extensions temp).serialize content) in
      if content_length < pow2 16 then (
        Some ({
          length = length ((ps_whole_ctls_extensions_allow_additional_internal ext_comp.tys ext_temp.expected_extensions temp).serialize content);
          content;
        } <: ctls_extensions_allow_additional bytes ext_comp.tys _ temp)
      ) else None
    ) else (
      match exts_additional with
      | [] -> Some (exts_expected_compressed <: (extensions_ctls_type ext_comp.tys get_ext_temp temp))
      | _ -> None
    )
  in

  let decompress (temp:ctls_template bytes) (ctls_exts:extensions_ctls_type ext_comp.tys get_ext_temp temp): option (list (extension bytes)) =
    let ext_temp = get_ext_temp temp in
    let compressed_expected_exts =
      if ext_temp.allow_additional then
        ctls_exts.content.expected_extensions
      else
        ctls_exts
    in
    let compressed_additional_exts: list (compressed_extension bytes ext_comp.tys temp) =
      if ext_temp.allow_additional then
        (ctls_exts <: ctls_extensions_allow_additional bytes ext_comp.tys ext_temp.expected_extensions temp).content.additional_extensions
      else
        []
    in
    let? expected_exts = decompress_expected_extensions ext_comp temp ext_temp.expected_extensions compressed_expected_exts in
    let? additional_exts = decompress_additional_extensions ext_comp temp compressed_additional_exts in
    let exts_expected_and_additional = extensions_expected_decompress expected_exts additional_exts in
    Some (extensions_predefined_decompress ext_temp.predefined_extensions exts_expected_and_additional)
  in

  {
    compress;
    decompress;
    decompress_compress = (fun temp exts ->
      match compress temp exts with
      | None -> ()
      | Some _ -> (
        let ext_temp = get_ext_temp temp in
        let Some exts_to_define = extensions_predefined_compress ext_temp.predefined_extensions exts in
        let Some (exts_expected, exts_additional) = extensions_expected_compress ext_temp.expected_extensions exts_to_define in
        extensions_expected_compress_correct ext_temp.expected_extensions exts_to_define;
        decompress_compress_expected_extensions ext_comp temp exts_expected;
        decompress_compress_additional_extensions ext_comp temp exts_additional;
        extensions_expected_decompress_compress ext_temp.expected_extensions exts_to_define;
        extensions_predefined_decompress_compress_eq ext_temp.predefined_extensions exts (extensions_expected_decompress exts_expected exts_additional)
      )
    );
    compress_decompress = (fun temp (ctls_exts:extensions_ctls_type ext_comp.tys get_ext_temp temp) ->
      match decompress temp ctls_exts with
      | None -> ()
      | Some _ -> (
        let ext_temp = get_ext_temp temp in
        let compressed_expected_exts =
          if ext_temp.allow_additional then
            ctls_exts.content.expected_extensions
          else
            ctls_exts
        in
        let compressed_additional_exts: list (compressed_extension bytes ext_comp.tys temp) =
          if ext_temp.allow_additional then
            (ctls_exts <: ctls_extensions_allow_additional bytes ext_comp.tys ext_temp.expected_extensions temp).content.additional_extensions
          else
            []
        in
        let Some expected_exts = decompress_expected_extensions ext_comp temp ext_temp.expected_extensions compressed_expected_exts in
        let Some additional_exts = decompress_additional_extensions ext_comp temp compressed_additional_exts in
        let exts_expected_and_additional = extensions_expected_decompress expected_exts additional_exts in
        extensions_predefined_compress_decompress ext_temp.predefined_extensions exts_expected_and_additional;
        extensions_expected_compress_decompress expected_exts additional_exts;
        compress_decompress_expected_extensions ext_comp temp ext_temp.expected_extensions compressed_expected_exts;
        compress_decompress_additional_extensions ext_comp temp compressed_additional_exts
      )
    );
  }
#pop-options

(*** Extensions: putting things together ***)

val to_extension_inner_compression:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #tls_type:Type0 -> #ctls_type:(ctls_template bytes -> Type0) ->
  parser_serializer_whole bytes tls_type ->
  compression bytes tls_type ctls_type equality_equivalence ->
  compression bytes (tls_extension_inner bytes) ctls_type equality_equivalence
let to_extension_inner_compression #bytes #bl #tls_type #ctls_type ps_tls_type comp =
  let compress (temp:ctls_template bytes) (x:tls_extension_inner bytes): option (ctls_type temp) =
    let? x_parsed = ps_tls_type.parse x.extension_data in
    comp.compress temp x_parsed
  in
  let decompress (temp:ctls_template bytes) (x:ctls_type temp): option (tls_extension_inner bytes) =
    let? x_decompressed = comp.decompress temp x in
    let x_bytes = ps_tls_type.serialize x_decompressed in
    if length x_bytes < pow2 16 then
      Some ({ extension_data = x_bytes; } <: tls_extension_inner bytes)
    else
      None
  in
  {
    compress;
    decompress;
    decompress_compress = (fun temp x ->
      match ps_tls_type.parse x.extension_data with
      | None -> ()
      | Some x_parsed -> (
        comp.decompress_compress temp x_parsed;
        ps_tls_type.serialize_parse_inv x.extension_data
      )
    );
    compress_decompress = (fun temp x ->
      match comp.decompress temp x with
      | None -> ()
      | Some x_decompressed ->
        comp.compress_decompress temp x;
        ps_tls_type.parse_serialize_inv x_decompressed
    );
  }

val one_extension_comp_for_self_delimiting_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #tls_type:Type0 ->
  ps_tls_type:parser_serializer_prefix bytes tls_type ->
  compression bytes (tls_extension_inner bytes) ((one_extension_type_for_self_delimiting_extension ps_tls_type).typ) equality_equivalence
let one_extension_comp_for_self_delimiting_extension #bytes #bl #tls_type ps_tls_type =
  to_extension_inner_compression (ps_prefix_to_ps_whole ps_tls_type) (no_compression tls_type)

val default_one_ext_comp:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  compression bytes (tls_extension_inner bytes) (default_one_ext_type.typ) equality_equivalence
let default_one_ext_comp #bytes #bl =
  no_compression (tls_extension_inner bytes)

val compute_ext_comp_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  orig:extension_origin -> ty:extension_type ->
  compression bytes (tls_extension_inner bytes) (compute_ext_type_aux unk orig ty).typ equality_equivalence
let compute_ext_comp_aux #bytes #bl unk origin ext_ty =
  match origin, ext_ty with
  | ClientHello, ET_key_share ->
    to_extension_inner_compression (ps_prefix_to_ps_whole ps_key_share_client_hello) key_share_client_hello_compression
  | ServerHello, ET_key_share ->
    to_extension_inner_compression (ps_prefix_to_ps_whole ps_key_share_server_hello) key_share_server_hello_compression
  | _, _ -> (
    match get_rfc8446_self_delimiting_extension_parser origin ext_ty with
    | Some (|tls_type, ps_tls_type|) ->
      one_extension_comp_for_self_delimiting_extension ps_tls_type
    | None ->
      match ext_ty with
      | ET_unknown_extension_type _ -> (
        match unk.self_delimiting_extension ext_ty with
        | Some (|ty, ps_ty|) -> to_extension_inner_compression (ps_prefix_to_ps_whole ps_ty) (no_compression ty)
        | None -> default_one_ext_comp
      )
      | _ -> default_one_ext_comp
  )

val compute_ext_comp:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_unknowns bytes ->
  orig:extension_origin ->
  ctls_extensions_comp bytes
let compute_ext_comp #bytes #bl unk origin =
  {
    tys = compute_ext_type unk origin;
    expected_comp = compute_ext_comp_aux unk origin;
    additional_comp = compute_ext_comp_aux unk origin;
  }

type ctls_extensions_ (bytes:Type0) {|bytes_like bytes|} (unk:ctls_unknowns bytes) (ext_orig:extension_origin) (t:ctls_template bytes) =
  extensions_ctls_type (compute_ext_comp unk ext_orig).tys (compute_ext_temp ext_orig) t

val extension_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  ext_orig:extension_origin ->
  compression bytes (list (extension bytes)) (ctls_extensions bytes unk ext_orig) extensions_eq
let extension_compression #bytes #bl unk ext_orig =
  let open FStar.Tactics in
  assert(ctls_extensions bytes unk ext_orig == ctls_extensions_ bytes unk ext_orig) by (trefl ());
  let res: compression bytes (list (extension bytes)) (ctls_extensions_ bytes unk ext_orig) extensions_eq = extensions_compression #bytes (compute_ext_comp unk ext_orig) (compute_ext_temp ext_orig) in
  let res: compression bytes (list (extension bytes)) (ctls_extensions bytes unk ext_orig) extensions_eq = res in
  res

(*** Theorem: `extenions_eq` preserves length ***)

#push-options "--fuel 1 --ifuel 1"
val count_filter:
  #a:eqtype ->
  x:a -> l:list a -> y:a ->
  Lemma
  (List.Tot.count y (List.Tot.filter (op_disEquality x) l) = (if x = y then 0 else List.Tot.count y l))
let rec count_filter #a x l y =
  match l with
  | [] -> ()
  | h::t -> count_filter x t y
#pop-options

#push-options "--fuel 1 --ifuel 1"
val length_filter:
  #a:Type ->
  p:(a -> bool) -> l:list a ->
  Lemma
  (List.Tot.length (List.Tot.filter p l) <= List.Tot.length l)
let rec length_filter #a p l =
  match l with
  | [] -> ()
  | h::t -> length_filter p t
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val bytes_length_filter:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ext:extension bytes -> exts:list (extension bytes) ->
  Lemma
  (bytes_length ps_extension exts = (bytes_length ps_extension (List.Tot.filter (op_disEquality ext) exts)) + ((prefixes_length (ps_extension.serialize ext)) `op_Multiply` (List.Tot.count ext exts)))
let rec bytes_length_filter #bytes #bl ext exts =
  match exts with
  | [] -> ()
  | h::t -> bytes_length_filter ext t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val bytes_length_extensions_eq:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  exts1:list (extension bytes) -> exts2:list (extension bytes) ->
  Lemma
  (requires exts1 `extensions_eq` exts2)
  (ensures bytes_length ps_extension exts1 == bytes_length ps_extension exts2)
  (decreases (List.Tot.length exts1))
let rec bytes_length_extensions_eq #bytes #bl exts1 exts2 =
  match exts1 with
  | [] -> ()
  | h1::t1 ->
    FStar.Classical.forall_intro (count_filter h1 exts1);
    FStar.Classical.forall_intro (count_filter h1 exts2);
    length_filter (op_disEquality h1) t1;
    bytes_length_extensions_eq (List.Tot.filter (op_disEquality h1) exts1) (List.Tot.filter (op_disEquality h1) exts2);
    bytes_length_filter h1 exts1;
    bytes_length_filter h1 exts2
#pop-options

(*** Certificate ***)

(*
#push-options "--fuel 1 --ifuel 1"
val assoc_inj_lemma_lemma:
  #a:eqtype -> #b:Type ->
  x:a -> y:b -> l:list (a & b) ->
  Lemma
  (requires List.Tot.memP (x, y) l)
  (ensures List.Tot.memP y (List.Tot.map snd l))
let rec assoc_inj_lemma_lemma #a #b x y l =
  match l with
  | _::t -> FStar.Classical.move_requires (assoc_inj_lemma_lemma x y) t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val assoc_inj_lemma:
  #a:eqtype -> #b:Type ->
  x1:a -> x2:a -> y:b -> l:list (a & b) ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map snd l) /\
    List.Tot.memP (x1, y) l /\
    List.Tot.memP (x2, y) l
  )
  (ensures x1 == x2)
let rec assoc_inj_lemma #a #b x1 x2 y l =
  match l with
  | (x',y')::t -> (
    eliminate (y == y') \/ (y =!= y')
    returns x1 == x2
    with _. (
      FStar.Classical.move_requires (assoc_inj_lemma_lemma x1 y) t;
      FStar.Classical.move_requires (assoc_inj_lemma_lemma x2 y) t
    ) and _. (
      assoc_inj_lemma x1 x2 y t
    )
  )
#pop-options

val assoc_inj:
  #a:eqtype -> #b:Type ->
  x1:a -> x2:a -> l:list (a & b) ->
  Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map snd l))
  (ensures (
    match List.Tot.assoc x1 l, List.Tot.assoc x2 l with
    | Some y1, Some y2 -> y1 == y2 ==> x1 == x2
    | _, _ -> True
  ))
let assoc_inj #a #b x1 x2 l =
  match List.Tot.assoc x1 l, List.Tot.assoc x2 l with
  | Some y1, Some y2 -> (
    List.Tot.assoc_memP_some x1 y1 l;
    List.Tot.assoc_memP_some x2 y2 l;
    introduce y1 == y2 ==> x1 == x2 with _. (
      assoc_inj_lemma x1 x2 y1 l
    )
  )
  | _, _ -> ()
*)

val swap:
  #a:Type -> #b:Type ->
  a & b ->
  b & a
let swap #a #b (x, y) = (y, x)

#push-options "--fuel 1 --ifuel 1"
val assoc_roundtrip_lemma_lemma:
  #a:eqtype -> #b:Type ->
  x:a -> y:b -> l:list (a & b) ->
  Lemma
  (requires List.Tot.memP (x, y) l)
  (ensures List.Tot.memP x (List.Tot.map fst l))
let rec assoc_roundtrip_lemma_lemma #a #b x y l =
  match l with
  | _::t -> FStar.Classical.move_requires (assoc_roundtrip_lemma_lemma x y) t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val assoc_roundtrip_lemma:
  #a:eqtype -> #b:Type0 ->
  x:a -> y:b -> l:list (a & b) ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    List.Tot.memP (x, y) l
  )
  (ensures
    List.Tot.assoc x l == Some y
  )
let rec assoc_roundtrip_lemma #a #b x y l =
  match l with
  | (x',y')::t -> (
    eliminate (x == x') \/ (x =!= x')
    returns List.Tot.assoc x l == Some y
    with _. (
      FStar.Classical.move_requires (assoc_roundtrip_lemma_lemma x y) t
    ) and _. (
      assoc_roundtrip_lemma x y t
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val map_fst_map_swap:
  #a:Type0 -> #b:Type0 ->
  l:list (a & b) ->
  Lemma
  (List.Tot.map fst (List.Tot.map swap l) == List.Tot.map snd l)
let rec map_fst_map_swap #a #b l =
  match l with
  | [] -> ()
  | h::t -> map_fst_map_swap t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val map_snd_map_swap:
  #a:Type0 -> #b:Type0 ->
  l:list (a & b) ->
  Lemma
  (List.Tot.map snd (List.Tot.map swap l) == List.Tot.map fst l)
let rec map_snd_map_swap #a #b l =
  match l with
  | [] -> ()
  | h::t -> map_snd_map_swap t
#pop-options

val assoc_roundtrip:
  #a:eqtype -> #b:eqtype ->
  x:a -> l:list (a & b) ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    List.Tot.no_repeats_p (List.Tot.map snd l)
  )
  (ensures (
    match List.Tot.assoc x l with
    | None -> True
    | Some y -> List.Tot.assoc y (List.Tot.map swap l) == Some x
  ))
let assoc_roundtrip #a #b x l =
  match List.Tot.assoc x l with
  | None -> ()
  | Some y -> (
    List.Tot.assoc_memP_some x y l;
    List.Tot.memP_map_intro swap (x, y) l;
    map_fst_map_swap l;
    map_snd_map_swap l;
    assoc_roundtrip_lemma y x (List.Tot.map swap l)
  )

val certificate_map_entry_to_pair:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  certificate_map_entry bytes ->
  (tls_bytes bytes (({min=1; max=(pow2 24)-1}))) & (tls_bytes bytes (({min=1; max=(pow2 24)-1})))
let certificate_map_entry_to_pair #bytes #bl entry =
  (entry.id, entry.cert_data)

#push-options "--fuel 1 --ifuel 1"
val noRepeats_to_no_repeats_p:
  #a:eqtype ->
  l:list a ->
  Lemma
  (requires List.Tot.noRepeats l)
  (ensures List.Tot.no_repeats_p l)
  [SMTPat (List.Tot.no_repeats_p l)]
let rec noRepeats_to_no_repeats_p #a l =
  match l with
  | [] -> ()
  | h::t -> noRepeats_to_no_repeats_p t
#pop-options

val get_known_certificates:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ctls_template bytes ->
  option (certificate_map bytes)
let get_known_certificates #bytes #bl t =
  get_template_element ps_certificate_map CTLSTET_known_certificates t

val assoc_list_well_formed:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  list ((tls_bytes bytes (({min=1; max=(pow2 24)-1}))) & (tls_bytes bytes (({min=1; max=(pow2 24)-1})))) ->
  bool
let assoc_list_well_formed #bytes #bl unk cert_map_list =
  List.Tot.noRepeats (List.Tot.map fst cert_map_list) &&
  List.Tot.noRepeats (List.Tot.map snd cert_map_list) &&
  List.Tot.for_all #(tls_bytes bytes ({min=1; max=((pow2 24)-1)})) unk.is_x509_certificate (List.Tot.map snd cert_map_list) &&
  List.Tot.for_all #(tls_bytes bytes ({min=1; max=((pow2 24)-1)})) (pred_not unk.is_x509_certificate) (List.Tot.map fst cert_map_list)

#push-options "--fuel 1 --ifuel 1"
val for_all_eliminate:
  #a:Type ->
  p:(a -> bool) -> l:list a -> x:a ->
  Lemma
  (requires List.Tot.for_all p l /\ List.Tot.memP x l)
  (ensures p x)
let rec for_all_eliminate #a p l x =
  match l with
  | [] -> ()
  | h::t -> FStar.Classical.move_requires (for_all_eliminate p t) x
#pop-options

#push-options "--fuel 1 --ifuel 1"
val map_swap_map_swap:
  #a:Type0 -> #b:Type0 ->
  l:list (a & b) ->
  Lemma
  (List.Tot.map swap (List.Tot.map swap l) == l)
let rec map_swap_map_swap #a #b l =
  match l with
  | [] -> ()
  | h::t -> map_swap_map_swap t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val memP_map_swap:
  #a:Type0 -> #b:Type0 ->
  x:(b & a) -> l:list (a & b) ->
  Lemma
  (requires List.Tot.memP x (List.Tot.map swap l))
  (ensures List.Tot.memP (swap x) l)
let rec memP_map_swap #a #b x l =
  match l with
  | [] -> ()
  | h::t -> FStar.Classical.move_requires (memP_map_swap x) t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val assoc_list_well_formed_implies_x509:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  id:(tls_bytes bytes (({min=1; max=(pow2 24)-1}))) -> cert:(tls_bytes bytes (({min=1; max=(pow2 24)-1}))) ->
  l:list ((tls_bytes bytes (({min=1; max=(pow2 24)-1}))) & (tls_bytes bytes (({min=1; max=(pow2 24)-1})))) ->
  Lemma
  (requires assoc_list_well_formed unk l /\ List.Tot.memP (id, cert) l)
  (ensures not (unk.is_x509_certificate id) /\ unk.is_x509_certificate cert)
let rec assoc_list_well_formed_implies_x509 #bytes #bl unk id cert l =
  match l with
  | [] -> ()
  | h::t -> FStar.Classical.move_requires (assoc_list_well_formed_implies_x509 unk id cert) t
#pop-options

val assoc_swap_implies_not_x509:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  cert:tls_bytes bytes (({min=1; max=(pow2 24)-1})) -> l:list ((tls_bytes bytes (({min=1; max=(pow2 24)-1}))) & (tls_bytes bytes (({min=1; max=(pow2 24)-1})))) ->
  Lemma
  (requires assoc_list_well_formed unk l)
  (ensures (
    match List.Tot.assoc cert (List.Tot.map swap l) with
    | None -> True
    | Some id -> not (unk.is_x509_certificate id)
  ))
let assoc_swap_implies_not_x509 #bytes #bl unk cert l =
  match List.Tot.assoc cert (List.Tot.map swap l) with
  | None -> ()
  | Some id -> (
    List.Tot.assoc_memP_some cert id (List.Tot.map swap l);
    List.Tot.memP_map_intro swap (id, cert) l;
    memP_map_swap (cert, id) l;
    assoc_list_well_formed_implies_x509 unk id cert l
  )

val assoc_implies_x509:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  id:tls_bytes bytes (({min=1; max=(pow2 24)-1})) -> l:list ((tls_bytes bytes (({min=1; max=(pow2 24)-1}))) & (tls_bytes bytes (({min=1; max=(pow2 24)-1})))) ->
  Lemma
  (requires assoc_list_well_formed unk l)
  (ensures (
    match List.Tot.assoc id l with
    | None -> True
    | Some id -> unk.is_x509_certificate id
  ))
let assoc_implies_x509 #bytes #bl unk id l =
  match List.Tot.assoc id l with
  | None -> ()
  | Some cert -> (
    List.Tot.assoc_memP_some id cert l;
    assoc_list_well_formed_implies_x509 unk id cert l
  )

#push-options "--fuel 1 --ifuel 1"
val cert_data_compression_lemma_none:
  #a:Type -> #b:eqtype ->
  x:b -> l:list (a&b) ->
  Lemma
  (requires List.Tot.memP x (List.Tot.map snd l))
  (ensures Some? (List.Tot.assoc x (List.Tot.map swap l)))
let rec cert_data_compression_lemma_none #a #b x l =
  match l with
  | [] -> ()
  | h::t -> FStar.Classical.move_requires (cert_data_compression_lemma_none x) t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val cert_data_decompression_lemma:
  #a:Type -> #b:eqtype ->
  x:b -> l:list (a&b) ->
  Lemma
  (requires Some? (List.Tot.assoc x (List.Tot.map swap l)))
  (ensures List.Tot.memP x (List.Tot.map snd l))
let rec cert_data_decompression_lemma #a #b x l =
  match l with
  | [] -> ()
  | h::t -> FStar.Classical.move_requires (cert_data_decompression_lemma x) t
#pop-options


val cert_data_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (tls_bytes bytes ({min=1; max=((pow2 24)-1)})) (no_template_dep (tls_bytes bytes ({min=1; max=((pow2 24)-1)}))) equality_equivalence
let cert_data_compression #bytes #bl unk =
  let compress (t:ctls_template bytes) (cert:tls_bytes bytes ({min=1; max=((pow2 24)-1)})): option (tls_bytes bytes ({min=1; max=((pow2 24)-1)})) =
    match get_known_certificates t with
    | None -> Some cert
    | Some cert_map -> (
      let cert_map_list = List.Tot.map certificate_map_entry_to_pair cert_map.entries in
      if not (assoc_list_well_formed unk cert_map_list && unk.is_x509_certificate cert) then
        None
      else (
        match List.Tot.assoc cert (List.Tot.map swap cert_map_list) with
        | None -> Some cert
        | Some res -> Some res
      )
    )
  in
  let decompress (t:ctls_template bytes) (cert:tls_bytes bytes ({min=1; max=((pow2 24)-1)})): option (tls_bytes bytes ({min=1; max=((pow2 24)-1)})) =
    match get_known_certificates t with
    | None -> Some cert
    | Some cert_map -> (
      let cert_map_list = List.Tot.map certificate_map_entry_to_pair cert_map.entries in
      if not (assoc_list_well_formed unk cert_map_list) then
        None
      else (
        if List.Tot.mem cert (List.Tot.map snd cert_map_list) then
          None
        else if unk.is_x509_certificate cert then
          Some cert
        else (
          match List.Tot.assoc cert cert_map_list with
          | None -> None
          | Some res -> Some res
        )
      )
    )
  in
  {
  compress;
  decompress;
  decompress_compress = (fun t cert ->
    match get_known_certificates t with
    | None -> ()
    | Some cert_map -> (
      let cert_map_list = List.Tot.map certificate_map_entry_to_pair cert_map.entries in
      if not (assoc_list_well_formed unk cert_map_list && unk.is_x509_certificate cert) then ()
      else (
        match List.Tot.assoc cert (List.Tot.map swap cert_map_list) with
        | None -> FStar.Classical.move_requires (cert_data_compression_lemma_none cert) cert_map_list
        | Some res ->
          map_fst_map_swap cert_map_list;
          map_snd_map_swap cert_map_list;
          assoc_roundtrip cert (List.Tot.map swap cert_map_list);
          map_swap_map_swap cert_map_list;
          assoc_swap_implies_not_x509 unk cert cert_map_list;
          assert(not (unk.is_x509_certificate res));
          introduce List.Tot.mem res (List.Tot.map snd cert_map_list) ==> False with _. (
            for_all_eliminate #(tls_bytes bytes ({min=1; max=((pow2 24)-1)})) unk.is_x509_certificate (List.Tot.map snd cert_map_list) res
          )
      )
    )
  );
  compress_decompress = (fun t cert ->
    match get_known_certificates t with
    | None -> ()
    | Some cert_map -> (
      let cert_map_list = List.Tot.map certificate_map_entry_to_pair cert_map.entries in
      if not (assoc_list_well_formed unk cert_map_list) then ()
      else (
        if List.Tot.mem cert (List.Tot.map snd cert_map_list) then ()
        else if unk.is_x509_certificate cert then (
          match List.Tot.assoc cert (List.Tot.map swap cert_map_list) with
          | None -> ()
          | Some res -> cert_data_decompression_lemma cert cert_map_list
        ) else (
          match List.Tot.assoc cert cert_map_list with
          | None -> ()
          | Some res -> (
            map_fst_map_swap cert_map_list;
            map_snd_map_swap cert_map_list;
            assoc_roundtrip cert cert_map_list;
            assoc_implies_x509 unk cert cert_map_list
          )
        )
      )
    )
  );
}

val certificate_entry_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (certificate_entry bytes) (no_template_dep (certificate_entry bytes)) equality_equivalence
let certificate_entry_compression #bytes #bl unk = {
  compress = (fun t cert_entry ->
    let? compressed_cert_data = (cert_data_compression unk).compress t cert_entry.public_key_or_cert_data in
    Some ({cert_entry with public_key_or_cert_data = compressed_cert_data})
  );
  decompress = (fun t cert_entry ->
    let? decompressed_cert_data = (cert_data_compression unk).decompress t cert_entry.public_key_or_cert_data in
    Some ({cert_entry with public_key_or_cert_data = decompressed_cert_data})
  );
  decompress_compress = (fun t cert_entry -> (cert_data_compression unk).decompress_compress t cert_entry.public_key_or_cert_data);
  compress_decompress = (fun t cert_entry -> (cert_data_compression unk).compress_decompress t cert_entry.public_key_or_cert_data);
}

val certificate_list_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1})) (no_template_dep (tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1}))) equality_equivalence
let certificate_list_compression #bytes #bl unk = {
  compress = (fun t (cert_list:tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1})) ->
    let? compressed_cert_list = (list_compression (certificate_entry_compression unk)).compress t cert_list in
    if bytes_length ps_certificate_entry compressed_cert_list < pow2 24 then
      Some (compressed_cert_list <: tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1}))
    else None
  );
  decompress = (fun t cert_list ->
    let? decompressed_cert_list = (list_compression (certificate_entry_compression unk)).decompress t cert_list in
    if bytes_length ps_certificate_entry decompressed_cert_list < pow2 24 then
      Some (decompressed_cert_list <: tls_list bytes ps_certificate_entry ({min=0; max=(pow2 24)-1}))
    else None
  );
  decompress_compress = (fun t cert_list ->
    (list_compression (certificate_entry_compression unk)).decompress_compress t cert_list;
    match (list_compression (certificate_entry_compression unk)).compress t cert_list with
    | None -> ()
    | Some compressed_cert_list -> (
      if not (bytes_length ps_certificate_entry compressed_cert_list < pow2 24) then ()
      else (
        let Some decompressed_cert_list = (list_compression (certificate_entry_compression unk)).decompress t compressed_cert_list in
        List.Tot.index_extensionality cert_list decompressed_cert_list
      )
    )
  );
  compress_decompress = (fun t cert_list ->
    (list_compression (certificate_entry_compression unk)).compress_decompress t cert_list
  );
}

val certificate_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (certificate bytes) (no_template_dep (certificate bytes)) equality_equivalence
let certificate_compression #bytes #bl unk = {
  compress = (fun t cert ->
    let? compressed_cert_list = (certificate_list_compression unk).compress t cert.certificate_list in
    Some ({cert with certificate_list = compressed_cert_list})
  );
  decompress = (fun t cert ->
    let? decompressed_cert_list = (certificate_list_compression unk).decompress t cert.certificate_list in
    Some ({cert with certificate_list = decompressed_cert_list})
  );
  decompress_compress = (fun t cert -> (certificate_list_compression unk).decompress_compress t cert.certificate_list);
  compress_decompress = (fun t cert -> (certificate_list_compression unk).compress_decompress t cert.certificate_list);
}

(*** Handshake messages ***)

val client_hello_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  equivalence (client_hello bytes)
let client_hello_equivalent #bytes #bl = fun ch1 ch2 ->
  ch1 == ({ch2 with extensions = ch1.extensions} <: client_hello bytes) /\
  extensions_eq ch1.extensions ch2.extensions

val client_hello_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (client_hello bytes) (ctls_client_hello bytes unk) client_hello_equivalent
let client_hello_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:client_hello bytes) ->
    if not (
      x.legacy_version = 0x0303 &&
      x.legacy_session_id = Comparse.empty #bytes &&
      x.legacy_compression_methods = from_nat #bytes 1 0
    ) then None
    else (
      let? random = random_compression.compress t x.random in
      let? cipher_suites = cipher_suites_compression.compress t x.cipher_suites in
      let? extensions = (extension_compression unk ClientHello).compress t x.extensions in
      Some ({
        random;
        cipher_suites;
        extensions;
      } <: ctls_client_hello bytes unk t)
    )
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_client_hello bytes unk t) ->
    let? random = random_compression.decompress t x.random in
    let? cipher_suites = cipher_suites_compression.decompress t x.cipher_suites in
    let? extensions = (extension_compression unk ClientHello).decompress t x.extensions in
    let extensions_length = bytes_length ps_extension extensions in
    if not (8 <= extensions_length && extensions_length < pow2 16) then None
    else (
      Some ({
        legacy_version = 0x0303;
        random;
        legacy_session_id = Comparse.empty #bytes;
        cipher_suites;
        legacy_compression_methods = from_nat #bytes 1 0;
        extensions;
      } <: client_hello bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:client_hello bytes) ->
    random_compression.decompress_compress t x.random;
    cipher_suites_compression.decompress_compress t x.cipher_suites;
    (extension_compression unk ClientHello).decompress_compress t x.extensions;

    match (extension_compression unk ClientHello).compress t x.extensions with
    | Some extensions -> (
      let (Some extensions') = (extension_compression unk ClientHello).decompress t extensions in
      bytes_length_extensions_eq x.extensions extensions'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_client_hello bytes unk t) ->
    random_compression.compress_decompress t x.random;
    cipher_suites_compression.compress_decompress t x.cipher_suites;
    (extension_compression unk ClientHello).compress_decompress t x.extensions
  );
}

/// For reasons of backward compatibility with middleboxes (see
/// Appendix D.4), the HelloRetryRequest message uses the same structure
/// as the ServerHello, but with Random set to the special value of the
/// SHA-256 of "HelloRetryRequest":
///
///   CF 21 AD 74 E5 9A 61 11 BE 1D 8C 02 1E 65 B8 91
///   C2 A2 11 16 7A BB 8C 5E 07 9E 09 E2 C8 A8 33 9C

let hello_retry_request_constant = 0xCF21AD74E59A6111BE1D8C021E65B891C2A211167ABB8C5E079E09E2C8A8339C

val is_true_server_hello:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  server_hello bytes ->
  bool
let is_true_server_hello #bytes #bl sh =
  sh.random <> from_nat #bytes 32 hello_retry_request_constant

type true_server_hello (bytes:eqtype) {|bytes_like bytes|} =
  sh:server_hello bytes{is_true_server_hello sh}

type false_server_hello (bytes:eqtype) {|bytes_like bytes|} =
  sh:server_hello bytes{~(is_true_server_hello sh)}

val server_hello_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  equivalence (server_hello bytes)
let server_hello_equivalent #bytes #bl = fun sh1 sh2 ->
  sh1 == ({sh2 with extensions = sh1.extensions} <: server_hello bytes) /\
  extensions_eq sh1.extensions sh2.extensions

val server_hello_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (true_server_hello bytes) (ctls_server_hello bytes unk) server_hello_equivalent
let server_hello_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:true_server_hello bytes) ->
    if not (
      x.legacy_version = 0x0303 &&
      x.legacy_session_id_echo = Comparse.empty #bytes &&
      x.legacy_compression_method = 0
    ) then None
    else (
      let? random = random_compression.compress t x.random in
      let? cipher_suite = cipher_suite_compression.compress t x.cipher_suite in
      let? extensions = (extension_compression unk ServerHello).compress t x.extensions in
      Some ({
        random;
        cipher_suite;
        extensions;
      } <: ctls_server_hello bytes unk t)
    )
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_server_hello bytes unk t) ->
    let? random = random_compression.decompress t x.random in
    let? cipher_suite = cipher_suite_compression.decompress t x.cipher_suite in
    let? extensions = (extension_compression unk ServerHello).decompress t x.extensions in
    let extensions_length = bytes_length ps_extension extensions in
    if not (6 <= extensions_length && extensions_length < pow2 16) then None
    else if not (random <> from_nat #bytes 32 hello_retry_request_constant) then None
    else (
      Some (({
        legacy_version = 0x0303;
        random;
        legacy_session_id_echo = Comparse.empty #bytes;
        cipher_suite;
        legacy_compression_method = 0;
        extensions;
      } <: server_hello bytes) <: true_server_hello bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:true_server_hello bytes) ->
    random_compression.decompress_compress t x.random;
    cipher_suite_compression.decompress_compress t x.cipher_suite;
    (extension_compression unk ServerHello).decompress_compress t x.extensions;

    match (extension_compression unk ServerHello).compress t x.extensions with
    | Some extensions -> (
      let (Some extensions') = (extension_compression unk ServerHello).decompress t extensions in
      bytes_length_extensions_eq x.extensions extensions'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_server_hello bytes unk t) ->
    random_compression.compress_decompress t x.random;
    cipher_suite_compression.compress_decompress t x.cipher_suite;
    (extension_compression unk ServerHello).compress_decompress t x.extensions
  );
}

val hello_retry_request_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (false_server_hello bytes) (ctls_hello_retry_request bytes unk) server_hello_equivalent
let hello_retry_request_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:false_server_hello bytes) ->
    if not (
      x.legacy_version = 0x0303 &&
      x.legacy_session_id_echo = Comparse.empty #bytes &&
      x.legacy_compression_method = 0
    ) then None
    else (
      let? cipher_suite = cipher_suite_compression.compress t x.cipher_suite in
      let? extensions = (extension_compression unk HelloRetryRequest).compress t x.extensions in
      Some ({
        cipher_suite;
        extensions;
      } <: ctls_hello_retry_request bytes unk t)
    )
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_hello_retry_request bytes unk t) ->
    let? cipher_suite = cipher_suite_compression.decompress t x.cipher_suite in
    let? extensions = (extension_compression unk HelloRetryRequest).decompress t x.extensions in
    let extensions_length = bytes_length ps_extension extensions in
    if not (6 <= extensions_length && extensions_length < pow2 16) then None
    else (
      Some (({
        legacy_version = 0x0303;
        random = from_nat #bytes 32 hello_retry_request_constant;
        legacy_session_id_echo = Comparse.empty #bytes;
        cipher_suite;
        legacy_compression_method = 0;
        extensions;
      } <: server_hello bytes) <: false_server_hello bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:false_server_hello bytes) ->
    cipher_suite_compression.decompress_compress t x.cipher_suite;
    (extension_compression unk HelloRetryRequest).decompress_compress t x.extensions;

    match (extension_compression unk HelloRetryRequest).compress t x.extensions with
    | Some extensions -> (
      let (Some extensions') = (extension_compression unk HelloRetryRequest).decompress t extensions in
      bytes_length_extensions_eq x.extensions extensions'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_hello_retry_request bytes unk t) ->
    cipher_suite_compression.compress_decompress t x.cipher_suite;
    (extension_compression unk HelloRetryRequest).compress_decompress t x.extensions
  );
}

val certificate_verify_compression:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  compression bytes (certificate_verify bytes) (ctls_certificate_verify bytes) equality_equivalence
let certificate_verify_compression #bytes #bl = {
  compress = (fun (t:ctls_template bytes) (x:certificate_verify bytes) ->
    let? algorithm = certificate_verify_algorithm_compression.compress t x.algorithm in
    let? signature = certificate_verify_signature_compression.compress t x.signature in
    Some ({
      algorithm;
      signature;
    } <: ctls_certificate_verify bytes t)
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_certificate_verify bytes t) ->
    let? algorithm = certificate_verify_algorithm_compression.decompress t x.algorithm in
    let? signature = certificate_verify_signature_compression.decompress t x.signature in
    Some ({
      algorithm;
      signature;
    } <: certificate_verify bytes)
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:certificate_verify bytes) ->
    certificate_verify_algorithm_compression.decompress_compress t x.algorithm;
    certificate_verify_signature_compression.decompress_compress t x.signature
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_certificate_verify bytes t) ->
    certificate_verify_algorithm_compression.compress_decompress t x.algorithm;
    certificate_verify_signature_compression.compress_decompress t x.signature
  );
}

val encrypted_extensions_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  equivalence (encrypted_extensions bytes)
let encrypted_extensions_equivalent #bytes #bl = fun ee1 ee2 ->
  ee1 == ({ee2 with extensions = ee1.extensions} <: encrypted_extensions bytes) /\
  extensions_eq ee1.extensions ee2.extensions

val encrypted_extensions_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (encrypted_extensions bytes) (ctls_encrypted_extensions bytes unk) encrypted_extensions_equivalent
let encrypted_extensions_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:encrypted_extensions bytes) ->
    let? extensions = (extension_compression unk EncryptedExtensions).compress t x.extensions in
    Some ({
      extensions;
    } <: ctls_encrypted_extensions bytes unk t)
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_encrypted_extensions bytes unk t) ->
    let? extensions = (extension_compression unk EncryptedExtensions).decompress t x.extensions in
    let extensions_length = bytes_length ps_extension extensions in
    if not (extensions_length < pow2 16) then None
    else (
      Some ({
        extensions;
      } <: encrypted_extensions bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:encrypted_extensions bytes) ->
    (extension_compression unk EncryptedExtensions).decompress_compress t x.extensions;
    match (extension_compression unk EncryptedExtensions).compress t x.extensions with
    | Some extensions -> (
      let (Some extensions') = (extension_compression unk EncryptedExtensions).decompress t extensions in
      bytes_length_extensions_eq x.extensions extensions'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_encrypted_extensions bytes unk t) ->
    (extension_compression unk EncryptedExtensions).compress_decompress t x.extensions
  );
}

val certificate_request_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  equivalence (certificate_request bytes)
let certificate_request_equivalent #bytes #bl = fun cr1 cr2 ->
  cr1 == ({cr2 with extensions = cr1.extensions} <: certificate_request bytes) /\
  extensions_eq cr1.extensions cr2.extensions

val certificate_request_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (certificate_request bytes) (ctls_certificate_request bytes unk) certificate_request_equivalent
let certificate_request_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:certificate_request bytes) ->
    let? extensions = (extension_compression unk CertificateRequest).compress t x.extensions in
    Some ({
      certificate_request_context = x.certificate_request_context;
      extensions;
    } <: ctls_certificate_request bytes unk t)
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_certificate_request bytes unk t) ->
    let? extensions = (extension_compression unk CertificateRequest).decompress t x.extensions in
    let extensions_length = bytes_length ps_extension extensions in
    if not (2 <= extensions_length && extensions_length < pow2 16) then None
    else (
      Some ({
        certificate_request_context = x.certificate_request_context;
        extensions;
      } <: certificate_request bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:certificate_request bytes) ->
    (extension_compression unk CertificateRequest).decompress_compress t x.extensions;
    match (extension_compression unk CertificateRequest).compress t x.extensions with
    | Some extensions -> (
      let (Some extensions') = (extension_compression unk CertificateRequest).decompress t extensions in
      bytes_length_extensions_eq x.extensions extensions'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_certificate_request bytes unk t) ->
    (extension_compression unk CertificateRequest).compress_decompress t x.extensions
  );
}

val handshake_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  equivalence (handshake bytes)
let handshake_equivalent #bytes #bl = fun h1 h2 ->
  h1.msg_type = h2.msg_type /\
  h1.length = h2.length /\ (
    match h1.msg_type with
    | HT_client_hello -> client_hello_equivalent #bytes h1.msg h2.msg
    | HT_server_hello -> server_hello_equivalent #bytes h1.msg h2.msg
    | HT_encrypted_extensions -> encrypted_extensions_equivalent #bytes h1.msg h2.msg
    | HT_certificate_request -> certificate_request_equivalent #bytes h1.msg h2.msg
    | _ -> h1.msg = h2.msg
  )

val handshake_equivalent_symmetric:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  hs1:handshake bytes -> hs2:handshake bytes ->
  Lemma
  (requires hs1 `handshake_equivalent` hs2)
  (ensures hs2 `handshake_equivalent` hs1)
let handshake_equivalent_symmetric #bytes #bl hs1 hs2 = ()

val handshake_equivalent_transitive:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  hs1:handshake bytes -> hs2:handshake bytes -> hs3:handshake bytes ->
  Lemma
  (requires hs1 `handshake_equivalent` hs2 /\ hs2 `handshake_equivalent` hs3)
  (ensures hs1 `handshake_equivalent` hs3)
let handshake_equivalent_transitive #bytes #bl hs1 hs2 hs3 = ()

val mk_ctls_transcript_handshake:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #t:ctls_template bytes ->
  unk:ctls_unknowns bytes ->
  msg_type:handshake_type -> msg:ctls_transcript_handshake_message bytes unk t msg_type ->
  option (ctls_transcript_handshake bytes unk t)
let mk_ctls_transcript_handshake #bytes #bl #t unk msg_type msg =
  let length = length ((ps_whole_ctls_transcript_handshake_message unk t msg_type).serialize msg) in
  if not (length < pow2 24) then None
  else (
    Some ({
      msg_type;
      length;
      msg;
    } <: ctls_transcript_handshake bytes unk t)
  )

val mk_handshake:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  msg_type:handshake_type -> msg:handshake_message bytes msg_type ->
  option (handshake bytes)
let mk_handshake #bytes #bl msg_type msg =
  let length = length ((ps_whole_handshake_message msg_type).serialize msg) in
  if not (length < pow2 24) then None
  else (
    Some ({
      msg_type;
      length;
      msg;
    } <: handshake bytes)
  )

val length_client_hello_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ch1:client_hello bytes -> ch2:client_hello bytes ->
  Lemma
  (requires ch1 `client_hello_equivalent` ch2)
  (ensures prefixes_length (ps_client_hello.serialize ch1) == prefixes_length (ps_client_hello.serialize ch2))
let length_client_hello_equivalent #bytes #bl ch1 ch2 =
  bytes_length_extensions_eq ch1.extensions ch2.extensions

val length_server_hello_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  sh1:server_hello bytes -> sh2:server_hello bytes ->
  Lemma
  (requires sh1 `server_hello_equivalent` sh2)
  (ensures prefixes_length (ps_server_hello.serialize sh1) == prefixes_length (ps_server_hello.serialize sh2))
let length_server_hello_equivalent #bytes #bl sh1 sh2 =
  bytes_length_extensions_eq sh1.extensions sh2.extensions

val length_encrypted_extensions_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ee1:encrypted_extensions bytes -> ee2:encrypted_extensions bytes ->
  Lemma
  (requires ee1 `encrypted_extensions_equivalent` ee2)
  (ensures prefixes_length (ps_encrypted_extensions.serialize ee1) == prefixes_length (ps_encrypted_extensions.serialize ee2))
let length_encrypted_extensions_equivalent #bytes #bl sh1 sh2 =
  bytes_length_extensions_eq sh1.extensions sh2.extensions

val length_certificate_request_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  ee1:certificate_request bytes -> ee2:certificate_request bytes ->
  Lemma
  (requires ee1 `certificate_request_equivalent` ee2)
  (ensures prefixes_length (ps_certificate_request.serialize ee1) == prefixes_length (ps_certificate_request.serialize ee2))
let length_certificate_request_equivalent #bytes #bl sh1 sh2 =
  bytes_length_extensions_eq sh1.extensions sh2.extensions

#push-options "--z3rlimit 25"
val handshake_compression:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  unk:ctls_unknowns bytes ->
  compression bytes (handshake bytes) (ctls_transcript_handshake bytes unk) handshake_equivalent
let handshake_compression #bytes #bl unk = {
  compress = (fun (t:ctls_template bytes) (x:handshake bytes) ->
    match x.msg_type with
    | HT_client_hello -> (
      let? msg = (client_hello_compression unk).compress t x.msg in
      mk_ctls_transcript_handshake unk HT_client_hello msg
    )
    | HT_server_hello -> (
      if is_true_server_hello #bytes x.msg then (
        let? msg = (server_hello_compression unk).compress t x.msg in
        mk_ctls_transcript_handshake unk HT_server_hello msg
      ) else (
        let? msg = (hello_retry_request_compression unk).compress t x.msg in
        mk_ctls_transcript_handshake unk HT_hello_retry_request_RESERVED msg
      )
    )
    | HT_hello_retry_request_RESERVED -> None
    | HT_certificate_verify -> (
      let? msg = certificate_verify_compression.compress t x.msg in
      mk_ctls_transcript_handshake unk HT_certificate_verify msg
    )
    | HT_certificate -> (
      let? msg = (certificate_compression unk).compress t x.msg in
      mk_ctls_transcript_handshake unk HT_certificate msg
    )
    | HT_encrypted_extensions -> (
      let? msg = (encrypted_extensions_compression unk).compress t x.msg in
      mk_ctls_transcript_handshake unk HT_encrypted_extensions msg
    )
    | HT_certificate_request -> (
      let? msg = (certificate_request_compression unk).compress t x.msg in
      mk_ctls_transcript_handshake unk HT_certificate_request msg
    )
    | _ -> (
      Some ({
        msg_type = x.msg_type;
        length = x.length;
        msg = x.msg;
      } <: ctls_transcript_handshake bytes unk t)
    )
  );
  decompress = (fun (t:ctls_template bytes) (x:ctls_transcript_handshake bytes unk t) ->
    match x.msg_type with
    | HT_client_hello -> (
      let? msg = (client_hello_compression unk).decompress t x.msg in
      mk_handshake HT_client_hello msg
    )
    | HT_server_hello -> (
      let? msg = (server_hello_compression unk).decompress t x.msg in
      if not (is_true_server_hello msg) then None
      else
        mk_handshake HT_server_hello msg
    )
    | HT_hello_retry_request_RESERVED -> (
      let? msg = (hello_retry_request_compression unk).decompress t x.msg in
      mk_handshake HT_server_hello msg
    )
    | HT_certificate_verify -> (
      let? msg = certificate_verify_compression.decompress t x.msg in
      mk_handshake HT_certificate_verify msg
    )
    | HT_certificate -> (
      let? msg = (certificate_compression unk).decompress t x.msg in
      mk_handshake HT_certificate msg
    )
    | HT_encrypted_extensions -> (
      let? msg = (encrypted_extensions_compression unk).decompress t x.msg in
      mk_handshake HT_encrypted_extensions msg
    )
    | HT_certificate_request -> (
      let? msg = (certificate_request_compression unk).decompress t x.msg in
      mk_handshake HT_certificate_request msg
    )
    | _ -> (
      Some ({
        msg_type = x.msg_type;
        length = x.length;
        msg = x.msg;
      } <: handshake bytes)
    )
  );
  decompress_compress = (fun (t:ctls_template bytes) (x:handshake bytes) ->
    match x.msg_type with
    | HT_client_hello -> (
      (client_hello_compression unk).decompress_compress t x.msg;
      match (client_hello_compression unk).compress t x.msg with
      | None -> ()
      | Some ctls_client_hello ->
        let Some (client_hello') = (client_hello_compression unk).decompress t ctls_client_hello in
        length_client_hello_equivalent x.msg client_hello'
    )
    | HT_server_hello -> (
      if is_true_server_hello #bytes x.msg then (
        (server_hello_compression unk).decompress_compress t x.msg;
        match (server_hello_compression unk).compress t x.msg with
        | None -> ()
        | Some ctls_server_hello ->
          let Some (server_hello') = (server_hello_compression unk).decompress t ctls_server_hello in
          length_server_hello_equivalent x.msg server_hello'
      ) else (
        (hello_retry_request_compression unk).decompress_compress t x.msg;
        match (hello_retry_request_compression unk).compress t x.msg with
        | None -> ()
        | Some ctls_hello_retry_request ->
          let Some (server_hello') = (hello_retry_request_compression unk).decompress t ctls_hello_retry_request in
          length_server_hello_equivalent x.msg server_hello'
      )
    )
    | HT_certificate_verify -> (
      certificate_verify_compression.decompress_compress t x.msg
    )
    | HT_certificate -> (
      (certificate_compression unk).decompress_compress t x.msg
    )
    | HT_encrypted_extensions -> (
      (encrypted_extensions_compression unk).decompress_compress t x.msg;
      match (encrypted_extensions_compression unk).compress t x.msg with
      | None -> ()
      | Some ctls_encrypted_extensions ->
        let Some (encrypted_extensions') = (encrypted_extensions_compression unk).decompress t ctls_encrypted_extensions in
        length_encrypted_extensions_equivalent x.msg encrypted_extensions'
    )
    | HT_certificate_request -> (
      (certificate_request_compression unk).decompress_compress t x.msg;
      match (certificate_request_compression unk).compress t x.msg with
      | None -> ()
      | Some ctls_certificate_request ->
        let Some (certificate_request') = (certificate_request_compression unk).decompress t ctls_certificate_request in
        length_certificate_request_equivalent x.msg certificate_request'
    )
    | _ -> ()
  );
  compress_decompress = (fun (t:ctls_template bytes) (x:ctls_transcript_handshake bytes unk t) ->
    match x.msg_type with
    | HT_client_hello -> (
      (client_hello_compression unk).compress_decompress t x.msg
    )
    | HT_server_hello -> (
      (server_hello_compression unk).compress_decompress t x.msg
    )
    | HT_hello_retry_request_RESERVED -> (
      (hello_retry_request_compression unk).compress_decompress t x.msg
    )
    | HT_certificate_verify -> (
      certificate_verify_compression.compress_decompress t x.msg
    )
    | HT_certificate -> (
      (certificate_compression unk).compress_decompress t x.msg
    )
    | HT_encrypted_extensions -> (
      (encrypted_extensions_compression unk).compress_decompress t x.msg
    )
    | HT_certificate_request -> (
      (certificate_request_compression unk).compress_decompress t x.msg
    )
    | _ -> ()
  );
}
#pop-options
