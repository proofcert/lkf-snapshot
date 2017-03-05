sig binary-unordered-examples.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig binary-unordered-fpc.

type assume_lemmas     int -> list bool -> o -> o.

type example           int -> list bool -> list bool -> list cert -> o.

type test              o.

type print_clause      int -> form -> o.

type test_all                 o.
type test_resol'       int -> o.
type test_resol        int -> o.
type test_reveal       int -> o.

type hope              int -> o.

%  Declarations for the steam roller theorem

type bi, ci, gi, si    i.
type dummy bool.
type is_animal, is_bird, is_cater, is_grain, is_plant, is_snail     i -> bool.
type much_smaller                                              i -> i -> bool.
