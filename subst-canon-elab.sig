sig subst-canon-elab.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig canonical-fpc.
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
type test_elab         int -> o.
type elab_all                 o.

type hope              int -> o.

