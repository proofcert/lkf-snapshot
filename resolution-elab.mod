%% Binary resolution with subsitution terms
module resolution-elab.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate binary-unordered-fpc.
accumulate binarysans-fpc.
accumulate binarysubst-fpc.
accumulate canonical-fpc.
accumulate pairing-fpc.

test_all :- example N _ _ _,
  term_to_string N Str, print Str, print "  ", 
            test_resol' N, print "\n", fail.

test_resol' N :- (test_resol N, print "#", fail); true.

test_resol N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start'' 1 Resol) B).

test_reveal N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start'' 1 Resol) B),
  term_to_string (start'' 1 Resol) String,
  print "Certificate = \n", print String, print "\n".

test_elab N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry ((start'' 1 Resol) <c> (start' 1 Elab)) B),
  term_to_string ((start'' 1 Resol) <c> (start' 1 Elab)) String,
  print "Certificate = \n", print String, print "\n".

elab_all :- example N _ _ _,
  term_to_string N Str, print Str, print "  ", 
            test_elab N, print "\n", fail.

assume_lemmas C nil    G :- G.
assume_lemmas C [L|Ls] G :-
   C' is C + 1, nnf conj+ disj- L L', ensure- L' L'',
   (lemma C L'' => assume_lemmas C' Ls G).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Elaboration predicates %
%%%%%%%%%%%%%%%%%%%%%%%%%%

% Right now, we leave the standard harness alone and we create separate
% predicates for each desired test, here.

% test_resol continues to be the baseline measurement: how much time does it
% take to check the unordered certificate?

% Given an output template Elab, take the first (uniquely numbered 1) example
% and elaborate from unordered resolution to it.
elab_resolution N Elab :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry ((start'' 1 Resol) <c> Elab) B).

% Like elab_resolution, but check the resulting, filled out template Elab after
% elaboration finishes. The time of checking this elaboration is:
%   time(elab_and_check) - time(elab_resolution).
% To avoid compiler limitations, this must take place in memory.
elab_and_check N Elab :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry ((start'' 1 Resol) <c> Elab) B),
  assume_lemmas C' Lemmas (lkf_entry Elab B).

% Like elab_resolution, but print size statistics and the elaborated certificate
% after checking/elaborating.
elab_and_print N Elab :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry ((start'' 1 Resol) <c> Elab) B),
  % Output certificate
%  print "Output certificate =\n",
%  term_to_string Elab StringElab,
%  print StringElab,
%  print "\n",
  % Example size
  print "Example size = ",
  size_example Clauses Lemmas Resol SizeExample,
  term_to_string SizeExample StringExample,
  print StringExample,
  print "\n",
  % Formula size
  print "Formula size = ",
  size_form B SizeB,
  term_to_string SizeB StringB,
  print StringB,
  print "\n",
  % Input certificate size
  print "Input size = ",
  size_cert (start'' 1 Resol) SizeInput,
  term_to_string SizeInput StringInput,
  print StringInput,
  print "\n",
  % Output certificate size
  print "Output size = ",
  size_cert Elab SizeOutput,
  term_to_string SizeOutput StringOutput,
  print StringOutput,
  print "\n".

elab_and_export N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry ((start'' 1 Resol) <c> (can 0 Elab)) B),
  % Formula
  print "Translated formula = ",
  print_form B,
  print "\n",
  % Maximal certificate
  print "Translated certificate = ",
  print_cert Elab,
  print "\n".

% The reference time.
check_unordered N :- test_resol N.

% Each elaboration is formulated easily in terms of the helper predicates and a
% standard template, subject to non-interference of constructors.
elab_to_sans N :- elab_resolution N (start' 1 Resol).
check_sans   N :- elab_and_check  N (start' 1 Resol).
print_sans   N :- elab_and_print  N (start' 1 Resol).

elab_to_subst N :- elab_resolution N (start 1 Resol).
check_subst   N :- elab_and_check  N (start 1 Resol).
print_subst   N :- elab_and_print  N (start 1 Resol).

% check and print are overkill: no need to assume lemmas (performance?)
elab_to_max N :- elab_resolution N (can 0 Elab).
check_max   N :- elab_and_check  N (can 0 Elab).
print_max   N :- elab_and_print  N (can 0 Elab).

%%%%%%%%%%%%%%%%%%%
% Size predicates %
%%%%%%%%%%%%%%%%%%%

%size_example X Y Z T :- announce (size_example X Y Z T).
%size_bool X Y :- announce (size_bool X Y).
%size_cert X Y :- announce (size_cert X Y).

% Some of these rely on assumptions about the form (and size) of possible
% indexes, etc., based on the definition of each FPC, under the condition
% that styles will not be mixed, something the typing discipline does not
% forbid.

% Lists

size_certs [] 1. % Adding nil.
size_certs [Cert | Certs] Size :-
	size_cert  Cert  SizeCert,
	size_certs Certs SizeCerts,
	Size is SizeCert + SizeCerts + 1. % Adding cons.

size_bools [] 1. % Adding nil.
size_bools [Bool | Bools] Size :-
	size_bool  Bool  SizeBool,
	size_bools Bools SizeBools,
	Size is SizeBool + SizeBools + 1. % Adding cons.

size_terms [] 1. % Adding nil.
size_terms [Term | Terms] Size :-
	size_term  Term  SizeTerm,
	size_terms Terms SizeTerms,
	Size is SizeTerm + SizeTerms + 1. % Adding cons.

% Base types

size_bool tt 1 & size_bool ff 1.
size_bool (ng Bool) Size :-
	size_bool Bool SizeBool,
	Size is SizeBool + 1.
size_bool (and   Bool1 Bool2) Size &
size_bool (or    Bool1 Bool2) Size &
size_bool (imp   Bool1 Bool2) Size &
size_bool (equiv Bool1 Bool2) Size :-
	size_bool Bool1 SizeBool1,
	size_bool Bool2 SizeBool2,
	Size is SizeBool1 + SizeBool2 + 1.
size_bool (forall BoolX) Size &
size_bool (exists BoolX) Size :-
	pi x\ size_bool (BoolX x) SizeBoolX,
	Size is SizeBoolX + 2. % Add connective and eigenvariable.

size_form (n Atm) Size &
size_form (p Atm) Size :-
	size_atm Atm SizeAtm,
	Size is SizeAtm + 1.
size_form f+ 1 & size_form f- 1 & size_form t+ 1 & size_form t- 1.
size_form (d- Form) Size &
size_form (d+ Form) Size :-
	size_form Form SizeForm,
	Size is SizeForm + 1.
size_form (Form1 &-& Form2) Size &
size_form (Form1 &+& Form2) Size &
size_form (Form1 !-! Form2) Size &
size_form (Form1 !+! Form2) Size :-
	size_form Form1 SizeForm1,
	size_form Form2 SizeForm2,
	Size is SizeForm1 + SizeForm2 + 1.
size_form (all  FormX) Size &
size_form (some FormX) Size :-
	pi x\ size_form (FormX x) SizeFormX,
	Size is SizeFormX + 2. % Add connective and eigenvariable.

% example

size_example Bools1 Bools2 Certs Size :-
	size_bools Bools1 SizeBools1,
	size_bools Bools2 SizeBools2,
	size_certs Certs SizeCerts,
	Size is SizeBools1 + SizeBools2 + SizeCerts.

% canonical

size_cert (can _ Can) Size :-
	size_can Can SizeCert,
	Size is SizeCert + 2.

size_can (cani (ix _) Can) Size :-
	size_can Can SizeCan,
	Size is SizeCan + 3.
size_can (can1 Can) Size :-
	size_can Can SizeCan,
	Size is SizeCan + 1.
size_can (can2 Can1 Can2) Size :-
	size_can Can1 SizeCan1,
	size_can Can2 SizeCan2,
	Size is SizeCan1 + SizeCan2 + 1.
size_can (canv CanX) Size :-
	pi x\ size_can (CanX x) SizeCanX,
	Size is SizeCanX + 2. % Counting x separately.
size_can (cant Term Can) Size :-
	size_term Term SizeTerm,
	size_can Can SizeCan,
	Size is SizeTerm + SizeCan + 1.
size_can (cana (ix _)) 3.
size_can can0 1.
size_can (canf Form Can1 Can2) Size :-
	size_form Form SizeForm,
	size_can Can1 SizeCan1,
	size_can Can2 SizeCan2,
	Size is SizeForm + SizeCan1 + SizeCan2 + 1.
size_can (canc _ Can) Size :-
	size_can Can SizeCan,
	Size is SizeCan + 2.

% binarysubst

size_cert (start  _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.
size_cert (rlist    Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 1.
size_cert (rlisti _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.

size_cert (factor _ _) 3.
size_cert (resolve _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.

size_cert (res _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (rex _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (rquant CertX) Size :-
	pi x\ size_cert (CertX x) SizeCertX,
	Size is SizeCertX + 2. % The abstraction is counted separately.
size_cert (subst Term Cert) Size :-
	size_term Term SizeTerm,
	size_cert Cert SizeCert,
	Size is SizeTerm + SizeCert + 1.

size_cert (factr _) 2.
size_cert fsmall    1.
size_cert small     1.
size_cert nsmall    1.
size_cert ismall    1.
size_cert rdone     1.
size_cert done      1.

% binarysans

size_cert (start'  _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.
size_cert (rlist'    Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 1.
size_cert (rlisti' _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.

size_cert (factor' _ _) 3.
size_cert (resolve' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (resolveX _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.

size_cert (res' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (rex' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.

size_cert (factr' _) 2.
size_cert fsmall'    1.
size_cert small'     1.
size_cert nsmall'    1.
size_cert ismall'    1.
size_cert rdone'     1.
size_cert done'      1.

% binary-unordered-fpc

size_cert (start''  _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.
size_cert (rlist''    Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 1.
size_cert (rlisti'' _ Certs) Size :- size_certs Certs SizeCerts, Size is SizeCerts + 2.

size_cert (factor'' _ _) 3.
size_cert (resolve'' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (resolveX' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.

size_cert (res'' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.
size_cert (rex'' _ Cert) Size :- size_cert Cert SizeCert, Size is SizeCert + 2.

size_cert (factr'' _) 2.
size_cert fsmall''    1.
size_cert small''     1.
size_cert nsmall''    1.
size_cert ismall''    1.
size_cert rdone''     1.
size_cert done''      1.

size_atm (atom _ Terms) Size :- size_terms Terms SizeTerms, Size is SizeTerms + 2.

% bool and term must be defined by the user; atm is wrapped by atom

% In order to count (unbound) variables when computing sizes, add a dummy in the
% private namespace, used in combination with the var predicate exclusively for
% this purpose.
var T :- not (not (T = dummy)).
size_term T 1 :- var T.
print_term T :- var T, print "Dummy".

%%%%%%%%%%%%%%%%%%
% OCaml printers %
%%%%%%%%%%%%%%%%%%

% As an alternative, define all these predicates and their clauses each in the
% module where the kinds are declared. Here, we keep everything together,
% knowing exactly which pieces we need to translate (i.e., the common framework
% and maximal certificates).

% Choices
%%%%%%%%%%

print_choice left :-
	print "Left".

print_choice right :-
	print "Right".

% Formulas
%%%%%%%%%%%

print_form (d- Form) :-
	print "NegativeDelay(",
	print_form Form,
	print ")".

print_form (d+ Form) :-
	print "PositiveDelay(",
	print_form Form,
	print ")".

print_form (Form1 &+& Form2) :-
	print "PositiveAnd(",
	print_form Form1,
	print ", ",
	print_form Form2,
	print ")".

print_form (Form1 !-! Form2) :-
	print "NegativeOr(",
	print_form Form1,
	print ", ",
	print_form Form2,
	print ")".

print_form (Form1 !+! Form2) :-
	print "PositiveOr(",
	print_form Form1,
	print ", ",
	print_form Form2,
	print ")".

% Quantifiers are the tricky part of formulas in the choice of bound variable
% names. The system handles this automatically.

print_form (some FormAbs) :- pi x\
	print "Exists(fun ",
	term_to_string x X, print X,
	print " -> ",
	print_form (FormAbs x),
	print ")".

print_form (all FormAbs) :- pi x\
	print "ForAll(fun ",
	term_to_string x X, print X,
	print " -> ",
	print_form (FormAbs x),
	print ")".

print_form f+ :-
	print "PositiveFalse".

print_form f- :-
	print "NegativeFalse".

print_form t+ :-
	print "PositiveTrue".

print_form t- :-
	print "NegativeTrue".

print_form (n Atom) :-
	print "NegativeAtom(",
	print_atm Atom,
	print ")".

print_form (p Atom) :-
	print "PositiveAtom(",
	print_atm Atom,
	print ")".

% Certificates
%%%%%%%%%%%%%%%

print_cert (can2 Cert1 Cert2) :-
	print "And(",
	print_cert Cert1,
	print ", ",
	print_cert Cert2,
	print ")".

print_cert (can1 Cert) :-
	print "Singleton(",
	print_cert Cert,
	print ")".

print_cert (canc Choice Cert) :-
	print "OrPositive(",
	print_choice Choice,
	print ", ",
	print_cert Cert,
	print ")".

print_cert (cant Term Cert) :-
	print "Exists(",
	print_term Term,
	print ", ",
	print_cert Cert,
	print ")".

% Quantifiers are the tricky part of formulas in the choice of bound variable
% names. The system handles this automatically.

print_cert (canv CertAbs) :- pi x\
	print "Forall(fun ",
	term_to_string x X, print X,
	print " -> ",
	print_cert (CertAbs x),
	print ")".

print_cert can0 :-
	print "End".

print_cert (cani Index Cert) :-
	print "Index(",
	print_index Index,
	print ", ",
	print_cert Cert,
	print ")".

print_cert (cana Index) :-
	print "Initial(",
	print_index Index,
	print ")".

print_cert (canf Form Cert1 Cert2) :-
	print "Cut(",
	print_form Form,
	print ", ",
	print_cert Cert1,
	print ", ",
	print_cert Cert2,
	print ")".

% Indexes
%%%%%%%%%%

print_index (ix Int) :-
	print "Idx(",
	term_to_string Int String, print String,
	print ")".

% Atoms
%%%%%%%%

print_atm (atom Name []) :-
	print_name Name.
print_atm (atom Name [Arg | Args]) :-
	print_name Name,
	print "(",
	print_terms [Arg | Args],
	print ")".

% Lists of terms
%%%%%%%%%%%%%%%%%

print_terms [T] :-
	print_term T.
print_terms [T | Ts] :-
	print_term T,
	print ", ",
	print_terms Ts.

%%%%%%%%%%%%%%%%%%%%%%%%%
% Problem-specific code %
%%%%%%%%%%%%%%%%%%%%%%%%%

% Define here:
%  - example 1
%  - pred_pname and fun_pname
%  - size_bool
%  - size_term, each terminated with a cut
%  - print_name, relating the string names of atoms with their OCaml identifiers
%  - print_term, each terminated with a cut
%  - ...

%%%%%%%%%%%%
% Colophon %
%%%%%%%%%%%%

% If the listing of possible terms is exhaustive and done well, and no other
% match avails, we must be treating an eigenvariable.

% In the appending translation scheme we are using, the colophon is generated as
% part of this translation, and is therefore commented out here.
%size_term X 1.
%print_term X :- term_to_string X String, print String.
