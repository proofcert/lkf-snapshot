sig p-distill.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig binarysans-fpc.
accum_sig binarysubst-fpc.
accum_sig pairing-fpc.

type assume_lemmas     int -> list bool -> o -> o.

type example           int -> list bool -> list bool -> list cert -> o.

type test              o.

type print_clause      int -> form -> o.

type test_all                 o.
type test_resol'       int -> o.
type test_resol        int -> o.
type test_reveal       int -> o.
type test_distill      int -> o.
type distill_all              o.

type hope              int -> o.

