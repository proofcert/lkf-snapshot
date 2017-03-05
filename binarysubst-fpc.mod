% Binary resolution with substitution terms in certificates.

% Note the addition of conditions such as "Cert = (cons _ _)" for
%   various constructors cons.  This constrains the system greatly and
%   allows for a more natural elaboration phase to be taken.  With
%   such constraints, the kernel should never be called with a
%   certificate that is a logic variable.

module binarysubst-fpc.

orC     (start Ct Certs) (start Ct  Certs).
falseC  (start Ct Certs) (start Ct  Certs).
storeC  (start Ct Certs) (start Ct' Certs) (idx Ct) :- inc Ct Ct'.
cutE    (start _ Certs) C1 C2 Cut :- cutE (rlist Certs) C1 C2 Cut.
cutE    (rlist (resolve K Cert::Certs)) Cert   (rlisti K Certs) Cut :- lemma K Cut, (Cert = (res _ _); Cert = (rquant _)).
cutE    (rlist (factor I K ::Certs)) (factr I) (rlisti K Certs) Cut :- lemma K Cut.

falseC  (rlist    Rs) (rlist Rs).
storeC  (rlisti K Rs) (rlist Rs) (idx K).
decideE (rlist []) rdone (idx I).
trueE   rdone.

%  Left premise
allC      (rquant Rs) Rs :- Rs = (x\ rquant (_ x)) ; Rs = (x\ res (_ x) (_ x)).
orC       (res I Cert) (res I Cert).
falseC    (res I Cert) (res I Cert).
storeC    (res I Cert) (res I Cert) lit.
decideE   (res I Cert) Cert (idx I) :- Cert = (subst _ _) ; Cert = (rex _ _).
someE     (subst T Cert) Cert T     :- Cert = (subst _ _) ; Cert = (rex _ _) ; Cert = done.

andE      (rex J Cert) small (rex J Cert).
andE      (rex J Cert) (rex J Cert) small.
releaseE  (rex J Cert) (rex J Cert).
storeC    (rex J Cert) (rex J Cert) pivot.
decideE   (rex I Cert) Cert (idx I) :-  Cert = (subst _ _) ; Cert = done.

andE      done small done.
andE      done done small.
initialE  done pivot.

andE      small  small  small.
trueE     small.
initialE  small  lit.
releaseE  small  nsmall.
storeC    nsmall nsmall immediate.
decideE   nsmall ismall lit.
initialE  ismall immediate.

% Describe the meaning of the factoring subproof.
allC      (factr I) (x\ factr I).
orC       (factr I) (factr I).
falseC    (factr I) (factr I).
storeC    (factr I) (factr I) lit.
decideE   (factr I) fsmall (idx I).
someE     fsmall fsmall T.
andE      fsmall small small.
trueE     fsmall.
initialE  fsmall lit.
