module Comparse.Tests.TacticNonGeneric

open Comparse.Bytes.Typeclass
open Comparse.Parser.Builtins
open Comparse.Parser.Derived
open Comparse.Tactic

type my_bytes = Seq.seq UInt8.t
instance _: bytes_like my_bytes = seq_u8_bytes_like

assume val test_ni: Type0
assume val test_ne: Type0
assume val test_ii: #bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ie: #bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ei: bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ee: bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_specific: Type0

assume val ps_test_ni: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes test_ni
assume val ps_test_ne: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes test_ne
assume val ps_test_ii: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ii #bytes)
assume val ps_test_ie: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ie #bytes)
assume val ps_test_ei: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ei bytes)
assume val ps_test_ee: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ee bytes)
assume val ps_test_specific: parser_serializer my_bytes test_specific

[@@ with_bytes my_bytes]
noeq type test_explicit_implicit = {
  f_ni: test_ni;
  f_ne: test_ne;
  f_ii: test_ii #my_bytes;
  f_ie: test_ie #my_bytes;
  f_ei: test_ei my_bytes;
  f_ee: test_ei my_bytes;
  f_specific: test_specific;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_explicit_implicit] (gen_parser (`test_explicit_implicit))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_explicit_implicit_is_well_formed] (gen_is_well_formed_lemma (`test_explicit_implicit))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_explicit_implicit_length] (gen_length_lemma (`test_explicit_implicit))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_explicit_implicit_serialize] (gen_serialize_lemma (`test_explicit_implicit))
#pop-options

[@@ is_parser; is_parser_for (`%string)]
assume val my_ps_string: parser_serializer_prefix my_bytes string

[@@ with_bytes my_bytes]
noeq type test_is_parser_for = {
  f_ni: test_ni;
  f_specific: test_specific;
  f_string: string;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_is_parser_for] (gen_parser (`test_is_parser_for))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_is_parser_for_is_well_formed] (gen_is_well_formed_lemma (`test_is_parser_for))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_is_parser_for_length] (gen_length_lemma (`test_is_parser_for))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_is_parser_for_serialize] (gen_serialize_lemma (`test_is_parser_for))
#pop-options
