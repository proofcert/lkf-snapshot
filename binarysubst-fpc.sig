sig binarysubst-fpc.
accum_sig lkf-certificates.
accum_sig lib.  % Need the inc predicate

% Deduced clauses are listed via the lemma predicate.
type lemma                 int -> form -> o.

type idx      int -> index. % Label of clauses which are never literals.
type lit             index. % Labels for literals that enter the side context.
type pivot           index. % Label for the stored pivot literal.
type immediate       index. % Used in small proofs

type start    int ->  list cert -> cert. % Needed just for the initial clerks.
type rlist            list cert -> cert. % List of resolution triples.
type rlisti   int ->  list cert -> cert. % Temporary linkage to share an index.

type factor           int -> int  -> cert. % A pair for factoring.
type resolve          int -> cert -> cert. % Introduce a resolvant subproof.

type res              int -> cert -> cert. % First index in resolvant
type rex              int -> cert -> cert. % Second index in resolvant
type rquant           (i -> cert) -> cert. % Eigenvariables allowed into certficate here.
type subst              i -> cert -> cert. % Use the following substitution term.

type factr                    int -> cert. % List of (the) clause on which to factor.
type fsmall                          cert. % Used to start the sync phase in factor checking.
type small                           cert.
type nsmall                          cert.
type ismall                          cert.
type rdone                           cert. % Must do an initial rule immediately.
type done                            cert. % End of the left premise of cut.

