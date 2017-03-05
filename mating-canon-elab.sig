sig mating-canon-elab.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig mating-fpc.
accum_sig canonical-fpc.
accum_sig pairing-fpc.

type test_all                  o.
type test                      int -> o.
type example                   int  -> bool -> o.
type check_mating              bool -> mating -> o.
type print_mating              mating -> o.
type print_nats                list nat -> o.
type print_nat                 nat -> o.
type convert_nat               nat -> int -> o.

type test_elab                 int -> o.
