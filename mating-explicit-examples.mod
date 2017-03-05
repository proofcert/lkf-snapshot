module mating-explicit-examples.
accumulate lib.
accumulate classical.
accumulate test-constants.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate mating-fpc.

check_mating B Mating List :- nnf conj- disj- B B', lkf_entry (mating zero nil Mating) B', join Mating nil List.

print_mating nil.
print_mating ((pr I J)::nil)    :- print "[", print_nat I, print ", ", print_nat J, print "]".
print_mating ((pr I J)::M::Ms) :-  print "[", print_nat I, print ", ", print_nat J, print "] ",
                                   print_mating (M::Ms).

print_nats nil :- print "\n".
print_nats (N::nil) :- print_nat N, print "\n".
print_nats (N::(N'::Ns)) :- print_nat N, print " ", print_nats (N'::Ns).

print_nat N :- convert_nat N I, term_to_string I Str, print Str.

convert_nat zero 0.
convert_nat (succ N) C :- convert_nat N D, C is D + 1.

test X :-
   example X F Mating,
   (sigma Str\ term_to_string X Str, print Str, print " "),
   if (check_mating F Mating List)
      (print "Success: ", print_mating List, print "\n")
      (print "Fail\n"), 
  fail.

test_all :-
  example X _ _,
  test X.

example 1 (or a (ng a))
(pr zero (succ zero) :: nil)
.

example 2 (equiv (equiv b a) (equiv a b))
(pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ zero))) (succ zero) :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ zero)) :: pr zero (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ zero) :: pr zero (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ zero))) (succ zero) :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ zero)) :: pr zero (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ zero) :: pr zero (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: nil)
.

example 3 (equiv (imp b a) (imp (ng a) (ng b)))
(pr zero (succ zero) :: pr (succ (succ zero)) zero :: pr (succ zero) zero :: pr zero (succ (succ zero)) :: nil)
.

example 4 (equiv (equiv b a) (equiv (ng a) (ng b)))
(pr (succ zero) (succ (succ zero)) :: pr zero (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ zero) :: pr zero (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ zero))) (succ zero) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ zero)) (succ zero) :: pr (succ (succ zero)) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ zero)) zero :: pr (succ (succ zero)) (succ zero) :: pr zero (succ (succ (succ zero))) :: pr (succ zero) (succ (succ (succ zero))) :: pr zero (succ (succ (succ zero))) :: nil)
.

example 5 (imp (imp (imp b a) b) b)
(pr (succ zero) zero :: pr (succ (succ zero)) zero :: nil)
.

example 6 (imp (equiv b a) (equiv a b))
(pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ zero))) (succ zero) :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ zero)) :: pr zero (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ zero) :: pr zero (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: nil)
.

example 7 (imp (equiv b a) (equiv (ng a) (ng b)))
(pr (succ (succ zero)) (succ zero) :: pr (succ (succ zero)) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ zero)) zero :: pr (succ (succ zero)) (succ zero) :: pr zero (succ (succ (succ zero))) :: pr (succ zero) (succ (succ (succ zero))) :: pr zero (succ (succ (succ zero))) :: nil)
.

example 8 (equiv b b)
(pr (succ zero) zero :: pr (succ zero) zero :: nil)
.

example 9 (imp (imp b a) (imp b a))
(pr (succ (succ zero)) zero :: pr zero (succ zero) :: nil)
.

example 10 (imp (and b a) (and b a))
(pr (succ (succ zero)) (succ zero) :: pr (succ (succ zero)) zero :: nil)
.

example 11 (imp (and b a) a)
(pr (succ (succ zero)) (succ zero) :: nil)
.

% The followineg are examples 8, 12, 17 (resp) from 
% Pelletier's article "Seventy-Five Problems for testineg Atomatic
% theorem Provers" (JAR 1986).
example 12 (imp (imp (imp b a) b) b)
(pr (succ zero) zero :: pr (succ (succ zero)) zero :: nil)
.

example 13 (equiv (equiv (equiv b a) c) (equiv b (equiv a c)))
(pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ zero) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ zero) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr zero (succ (succ (succ zero))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ zero) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr zero (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ zero) (succ (succ (succ zero))) :: pr zero (succ (succ (succ zero))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ zero))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ zero) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr zero (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr zero (succ (succ (succ zero))) :: pr zero (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ zero)) :: pr (succ (succ zero)) (succ (succ (succ zero))) :: pr (succ (succ zero)) (succ zero) :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr zero (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ zero)) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr zero (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ (succ zero))))) (succ zero) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ zero)) :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ zero) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ zero)) :: pr (succ (succ zero)) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ zero) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ zero)))) (succ (succ zero)) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ zero))))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ zero)) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ zero)))) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ zero) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ zero)) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) (succ (succ (succ zero))) :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ (succ (succ (succ (succ zero)))))) zero :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ (succ (succ zero))) (succ (succ (succ (succ (succ zero))))) :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ (succ (succ (succ zero))))) zero :: pr (succ (succ zero)) (succ (succ (succ (succ zero)))) :: pr (succ zero) (succ (succ (succ (succ zero)))) :: nil)
.

example 14 (equiv (imp (and b (imp a c)) d)
                  (and (or (ng b) (or a d))
                       (or (ng b) (or (ng c) d))))
(pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ zero)))) zero :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ zero)) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ (succ (succ (succ zero)))) (succ zero) :: pr (succ zero) (succ (succ (succ zero))) :: pr zero (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: pr (succ zero) (succ (succ zero)) :: pr (succ (succ (succ zero))) zero :: pr (succ (succ (succ zero))) zero :: pr (succ zero) (succ (succ (succ zero))) :: pr (succ (succ (succ zero))) zero :: pr zero (succ zero) :: pr zero (succ zero) :: nil)
.

example 15 (imp a (and a a))
(pr (succ zero) zero :: pr (succ zero) zero :: nil)
.

/*  Not tautologies
example 20 (equiv (equiv b a) (equiv (ng c) (ng b))). 
example 21 (equiv b a).
example 22 (equiv (equiv b a) (equiv d c)).
example 23 (and Ex4 c) :- example 4 Ex4.
*/
