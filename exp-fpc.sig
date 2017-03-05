% This is a non-standard header.  Get this fpc to conform.
sig exp-fpc.

accum_sig lkf-certificates.
accum_sig lib.
accum_sig classical.

kind pair     type -> type -> type.
type pr       A -> B -> pair A B.

kind et       type.  % expansion trees
kind qet      type.  % quantified expansion trees (leading introduction of select vars)

type idx             form -> index.
typeabbrev assoc     list (pair i i).     % Association of internal/external eigenvariables
typeabbrev subExp    list (pair i et).    % Expansions for a node
typeabbrev context   list (pair form et). % Basic elements of contexts

typeabbrev form_ets  pair (i -> form) subExp. % pairing of the body of an existential
                                              % with a subExp (saying how to instantiate).
type eIntro            (i -> qet) -> qet.
type eC                et -> qet.

type eTrue, eFalse     et.
type eLit              et.
type eAnd, eOr	       et -> et -> et.
type eAll              i  -> et -> et.	
type eSome             subExp    -> et.
type eSomeOrd          subExp    -> et.

type astate, dstate    assoc -> context -> context        -> cert.
type sstate            assoc -> context -> (pair form et) -> cert.

type translate_term    assoc -> i -> i -> o.
