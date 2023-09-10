module Comparse.Tests.TacticStress

open Comparse.Bytes.Typeclass
open Comparse.Parser.Builtins
open Comparse.Parser.Derived
open Comparse.Tactic

assume val test_ty: Type0

assume val ps_test_ty: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes test_ty

noeq type test_big_record (bytes:Type0) {|bytes_like bytes|} = {
  f0:  test_ty;f1:  test_ty;f2:  test_ty;f3:  test_ty;f4:  test_ty;f5:  test_ty;f6:  test_ty;f7:  test_ty;
  f8:  test_ty;f9:  test_ty;f10: test_ty;f11: test_ty;f12: test_ty;f13: test_ty;f14: test_ty;f15: test_ty;
  f16: test_ty;f17: test_ty;f18: test_ty;f19: test_ty;f20: test_ty;f21: test_ty;f22: test_ty;f23: test_ty;
  f24: test_ty;f25: test_ty;f26: test_ty;f27: test_ty;f28: test_ty;f29: test_ty;f30: test_ty;f31: test_ty;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_big_record] (gen_parser (`test_big_record))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_big_record_is_well_formed] (gen_is_well_formed_lemma (`test_big_record))
#pop-options

// This one is a bit hard on the SMT, with the core typechecker
//#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0' --z3rlimit 500"
//%splice [ps_test_big_record_length] (gen_length_lemma (`test_big_record))
//#pop-options

#push-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_big_record_serialize] (gen_serialize_lemma (`test_big_record))
#pop-options

noeq type test_big_sum (bytes:Type0) {|bytes_like bytes|} =
  | TestBigSum_0:  test_ty -> test_big_sum bytes
  | TestBigSum_1:  test_ty -> test_big_sum bytes
  | TestBigSum_2:  test_ty -> test_big_sum bytes
  | TestBigSum_3:  test_ty -> test_big_sum bytes
  | TestBigSum_4:  test_ty -> test_big_sum bytes
  | TestBigSum_5:  test_ty -> test_big_sum bytes
  | TestBigSum_6:  test_ty -> test_big_sum bytes
  | TestBigSum_7:  test_ty -> test_big_sum bytes
  | TestBigSum_8:  test_ty -> test_big_sum bytes
  | TestBigSum_9:  test_ty -> test_big_sum bytes
  | TestBigSum_10: test_ty -> test_big_sum bytes
  | TestBigSum_11: test_ty -> test_big_sum bytes
  | TestBigSum_12: test_ty -> test_big_sum bytes
  | TestBigSum_13: test_ty -> test_big_sum bytes
  | TestBigSum_14: test_ty -> test_big_sum bytes
  | TestBigSum_15: test_ty -> test_big_sum bytes

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_big_sum] (gen_parser (`test_big_sum))
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_big_sum_is_well_formed] (gen_is_well_formed_lemma (`test_big_sum))
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_big_sum_length] (gen_length_lemma (`test_big_sum))
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=0'"
%splice [ps_test_big_sum_serialize] (gen_serialize_lemma (`test_big_sum))
#pop-options
