sig resolution-elab.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig binary-unordered-fpc.
accum_sig binarysans-fpc.
accum_sig binarysubst-fpc.
accum_sig canonical-fpc.
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

type elab_resolution   int -> cert -> o.
type elab_and_check    int -> cert -> o.
type elab_and_print    int -> cert -> o.
% Export to OCaml
type elab_and_export   int -> o.

type check_unordered   int -> o.
type elab_to_sans      int -> o.
type check_sans        int -> o.
type print_sans        int -> o.
type elab_to_subst     int -> o.
type check_subst       int -> o.
type print_subst       int -> o.
type elab_to_max       int -> o.
type check_max         int -> o.
type print_max         int -> o.

type size_example      list bool -> list bool -> list cert -> int -> o.

type size_cert         cert -> int -> o.
type size_certs        list cert -> int -> o.

type size_can          can -> int -> o.

type size_atm          atm -> int -> o.
type size_term         i -> int -> o.
type size_terms        list i -> int -> o.
type size_bool         bool -> int -> o.
type size_bools        list bool -> int -> o.
type size_form         form -> int -> o.

% Detect variables during counting
type var               i -> o.
type dummy             i.

% Export to OCaml
type print_form     form -> o.
type print_index    index -> o.
type print_cert     can -> o.
type print_atm      atm -> o.
type print_choice   choice -> o.
type print_terms    list i -> o.
% User part
type print_name     string -> o.
type print_term     i -> o.

%%%%%%%%%%%%%%%%%%%%%%%%%
% Problem-specific code %
%%%%%%%%%%%%%%%%%%%%%%%%%

