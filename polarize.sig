% The predicates here encode unpolarized (regular) logical
% expressions into polarized expressions. 

% The nnf predicate is used to map classical formulas into the
%  kernel's abstract datatype of formulas.  The client must provide an
%  explicit mapping from atomic boolean formulas into the atm type
%  which is given by the bool_atm predicate.

sig polarize.
accum_sig lib.
accum_sig lkf-formulas.
accum_sig classical.

type atom   string -> list i -> atm.

type nnf    (form -> form -> form -> o) ->
            (form -> form -> form -> o) -> bool -> form -> o.


