%% Binary resolution with subsitution terms
module binarysans-examples.
accumulate lib.
accumulate classical.
accumulate test-constants.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate binarysans-fpc.

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
  assume_lemmas C' Lemmas (lkf_entry (start' 1 Resol) B).

test_reveal N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start' 1 Resol) B),
  term_to_string (start' 1 Resol) String,
  print "Certificate = \n", print String, print "\n".

assume_lemmas C nil    G :- G.
assume_lemmas C [L|Ls] G :-
   C' is C + 1, nnf conj+ disj- L L', ensure- L' L'',
   (lemma C L'' => assume_lemmas C' Ls G).

% The following are example certificates from the client's point-of-view.
% There are three lists:
%  1. The list of clauses, which when taken as hypothesis, yields
%     a contradiction. 
%  2. A list of "lemma".  These are new clauses that are resolvants
%     of previous clauses.
% 3. The certificate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%   Propositional examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%  A single propositional letter

example 10 
  [a,
  (ng a)]
  [ff]
  [resolve' 3 (res' 1 (rex' 2 done'))].

example 20
  [(ng a),
   a]
  [ff]
  [resolve' 3 (res' 2 (rex' 1 done'))].

example 30 
  [(or a ff),
   (or (ng a) ff)]
  [ff]
  [resolve' 3 (res' 1 (rex' 2 done'))].

example 40   % This one fails.  One must factor explicitly to proceed.
  [(or a a),
   (or (ng a) (ng a))]
  [ff]
  [resolve' 3 (res' 1 (rex' 2 done'))].

example 41   % This variant works but leaves lots of backtrack points.
  [(or a a),            % 1
   (or (ng a) (ng a))]  % 2
  [a,                   % 3
   (ng a),              % 4
   ff]                  % 5
  [factor' 1 3, 
   resolve' 4 (res' 3 (rex' 2 done')),
   resolve' 5 (res' 3 (rex' 4 done'))].

example 42   % This variant is a "permutation" of above but with fewer backtrack points.
  [(or a a),            % 1
   (or (ng a) (ng a))]  % 2
  [a,                   % 3
   (ng a),              % 4
   ff]                  % 5
  [factor' 1 3, 
   factor' 2 4,
   resolve' 5 (res' 3 (rex' 4 done'))].

example 43
  [(or a a),           % 1
   (ng a)]             % 2
  [a,                  % 3
   ff]                 % 4
  [factor' 1 3, 
   resolve' 4 (res' 3 (rex' 2 done'))].

example 44 % dual of 40
  [(or (ng a) (ng a)),      % 1
   a]                       % 2
  [(ng a),                  % 3
   ff]                      % 4
  [factor' 1 3, 
   resolve' 4 (res' 2 (rex' 3 done'))].

example 45 % not checkable
  [a,                  % 1
   (ng a)]             % 2
  [(or a a),           % 3
   ff]                 % 4
  [factor' 1 3, 
   resolve' 4 (res' 3 (rex' 2 done'))].

%%%%  Multiple propositional letters

example 70 
  [(or a b),           % 1
   (or (ng a) e),      % 2
   (ng b),             % 3
   (ng e)]             % 4
  [(or b e),           % 5
   e,                  % 6
   ff]                 % 7
  [resolve'  5 (res' 1 (rex' 2 done')),
   resolve'  6 (res' 5 (rex' 3 done')),
   resolve'  7 (res' 6 (rex' 4 done'))].

example 71
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (or (ng a) b),      % 3
   (or (ng a) (ng b))] % 4
  [(or a a),           % 5
   a,                  % 6
   (or (ng a) (ng a)), % 7
   (ng a),             % 8
   ff]                 % 9
  [resolve' 5 (res' 1 (rex' 2 done')),
   factor' 5 6, 
   resolve' 7 (res' 3 (rex' 4 done')),
   factor' 7 8,
   resolve' 9 (res' 6 (rex' 8 done'))].

example 72  % Just like 71 but factoring is moved into the resol method
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (or (ng a) b),      % 3
   (or (ng a) (ng b))] % 4
  [a,                  % 5
   (ng a),             % 6
   ff]                 % 7
  [resolve' 5 (res' 1 (rex' 2 done')),
   resolve' 6 (res' 3 (rex' 4 done')),
   resolve' 7 (res' 5 (rex' 6 done'))].

example 80
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [(or a a),           % 4
   a,                  % 5
   ff]                 % 6
  [resolve' 4 (res' 1 (rex' 2 done')),
   factor' 4 5,
   resolve' 6 (res' 5 (rex' 3 done'))].

example 81   % A variation on 80.  Permute the rules to eliminate "a" 
             % first so it is not appearring twice in the combined side formulas.
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [b,                  % 4
   (ng b),             % 5
   ff]                 % 6
  [resolve' 4 (res' 1 (rex' 3 done')), 
   resolve' 5 (res' 2 (rex' 3 done')),
   resolve' 6 (res' 4 (rex' 5 done'))].

example 82  % Another variation but the factoring is done internally.
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [a,                  % 4
   ff]                 % 5
  [resolve' 4 (res' 1 (rex' 2 done')),
   resolve' 5 (res' 4 (rex' 3 done'))].

example 90
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [a,                  % 4
   ff]                 % 5
  [resolve' 4 (res' 1 (rex' 2 done')), 
   resolve' 5 (res' 4 (rex' 3 done'))].

example 91
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [(or (or a a) (or a a)),    % 4  It is repetition here that causes backtracking
   a,                  % 5
   ff]                 % 6
  [resolve' 4 (res' 1 (rex' 2 done')), 
   factor' 4 5,
   resolve' 6 (res' 5 (rex' 3 done'))].

% Conjectures: The following are for the propositional case.

%  (1) If there repeated literals in the resolvant, then there are
%      backtrack points that are not useful to have.
%  (2) If there are repeated literals in the combined side formulas,
%      then there are also backtrack points.

% The use of implicit factoring (write down the resolvant without
% repeats) can eliminate (1) backtracking.  Use of explicit factoring
% (as defined in this FPC) is too late to get rid of backtrack
% points.

% Eliminating (2) seems hard in this framework.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Simple quantificational examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example 100 
  [(r z),                           % 1
   (forall x\ or (ng (r x)) (t x)), % 2
   (ng (t z))]                      % 3
  [(t z),                           % 4
   ff]                              % 5
  [resolve' 4 (res' 1 (rex' 2 done')),
   resolve' 5 (res' 4 (rex' 3 done'))].

example 110 
 [(r z),                                            % 1
  (forall x\ or (ng (r x)) (r (k x))),              % 2
  (ng (r (k (k (k (k z))))))]                       % 3
 [(forall x\ or (ng (r x)) (r (k (k x)))),          % 4
  (forall x\ or (ng (r x)) (r (k (k (k (k x)))))),  % 5
  (r (k (k (k (k z))))),                            % 6
  ff]                                               % 7
[ resolve' 4 (res' 2 (rex' 2 done')),
  resolve' 5 (res' 4 (rex' 4 done')),
  resolve' 6 (res' 1 (rex' 5 done')),
  resolve' 7 (res' 6 (rex' 3 done'))].

example 111 % same a 110 but without explicit subterm
 [(r z),                                            % 1
  (forall x\ or (ng (r x)) (r (k x))),              % 2
  (ng (r (k (k (k (k z))))))]                       % 3
 [(forall x\ or (ng (r x)) (r (k (k x)))),          % 4
  (forall x\ or (ng (r x)) (r (k (k (k (k x)))))),  % 5
  (r (k (k (k (k z))))),                            % 6
  ff]                                               % 7
[ resolve' 4 (res' 2 (rex' 2 done')),
  resolve' 5 (res' 4 (rex' 4 done')),
  resolve' 6 (res' 1 (rex' 5 done')),
  resolve' 7 (res' 6 (rex' 3 done'))].

example 120
 [(r z),                                % 1
  (forall x\ or (ng (r x)) (r (k x))),  % 2
  (ng (r (k (k (k (k z))))))]           % 3
 [(r (k z)),                            % 4
  (r (k (k z))),                        % 5
  (r (k (k (k z)))),                    % 6
  (r (k (k (k (k z))))),                % 7
  ff]                                   % 8
[ resolve' 4 (res' 1 (rex' 2 done')),
  resolve' 5 (res' 4 (rex' 2 done')),
  resolve' 6 (res' 5 (rex' 2 done')),
  resolve' 7 (res' 6 (rex' 2 done')),
  resolve' 8 (res' 7 (rex' 3 done'))].

example 130
[ (is_wolf wi),                            % 1
  (forall x\ forall y\ or (ng (is_wolf  x)) (or (ng (is_fox y)) (ng (eats x y)))), % 2
  (is_fox fi),                             % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve' 5 (res' 1 (rex' 2 done')),
  resolve' 6 (res' 3 (rex' 5 done')),
  resolve' 7 (res' 4 (rex' 6 done'))].

example 131
[ (is_wolf  wi),                           % 1
  (forall x\ forall y\ (or (ng (is_wolf  x)) (or (ng (is_fox y)) (ng (eats x y))))), % 2
  (is_fox   fi),                           % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve' 5 (res' 1 (rex' 2 done')),
  resolve' 6 (res' 3 (rex' 5 done')),
  resolve' 7 (res' 4 (rex' 6 done'))].

example 132
[ (is_wolf  wi),                           % 1
  (or (ng (is_wolf  wi)) (or (ng (is_fox fi)) (ng (eats wi fi)))), % 2
  (is_fox   fi),                           % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve' 5 (res' 1 (rex' 2 done')),
  resolve' 6 (res' 3 (rex' 5 done')),
  resolve' 7 (res' 4 (rex' 6 done'))].

example 133
[ a,                              % 1
  (or (ng a) (or (ng b) (ng c))), % 2
  b,                              % 3
  c]                              % 4
[ (or (ng b) (ng c)),             % 5
  (ng c),                         % 6
  ff]                             % 7
[ resolve' 5 (res' 1 (rex' 2 done')),
  resolve' 6 (res' 3 (rex' 5 done')),
  resolve' 7 (res' 4 (rex' 6 done'))].

example 134
[ a,                              % 1
  (or (ng a) (ng b)),             % 2
  b]                              % 3
[ (ng b),                         % 4
  ff]                             % 5
[ resolve' 4 (res' 1 (rex' 2 done')),
  resolve' 5 (res' 3 (rex' 4 done'))].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Steam roller example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun_pname bi "bi" [].
fun_pname ci "ci" [].
fun_pname gi "gi" [].
fun_pname si "si" [].

pred_pname (is_animal X) "is_animal" [X].
pred_pname (is_bird   X) "is_bird"   [X].
pred_pname (is_cater  X) "is_cater"  [X].
pred_pname (is_grain  X) "is_grain"  [X].
pred_pname (is_plant  X) "is_plant"  [X].
pred_pname (is_snail  X) "is_snail"  [X].
pred_pname (much_smaller X Y) "much_smaller" [X,Y].
pred_pname dummy         "dummy"     [].

example 200 % steamroller
[
	(forall (x\ or (ng(is_wolf  x)) (is_animal x))), % 1
	(forall (x\ or (ng(is_fox   x)) (is_animal x))), % 2
	(forall (x\ or (ng(is_bird  x)) (is_animal x))), % 3
	(forall (x\ or (ng(is_cater x)) (is_animal x))), % 4
	(forall (x\ or (ng(is_snail x)) (is_animal x))), % 5
	(is_wolf  wi), % 6
	(is_fox   fi), % 7
	(is_bird  bi), % 8
	(is_cater ci), % 9
	(is_snail si), % 10
	(is_grain gi), % 11
	(forall (x\ or (ng(is_grain x)) (is_plant  x))), % 12
	(forall (x\ forall (y\ forall (z\ forall (v\ or (ng(is_animal x)) (or (ng(is_plant y)) (or (ng(is_animal z)) (or (ng(is_plant v)) (or (ng(eats x y)) (or (ng(much_smaller z x)) (or (ng(eats z v)) (eats x z)))))))))))), % 13
	(forall (x\ forall (y\ or (ng(is_cater x)) (or (ng(is_bird  y)) (much_smaller x y))))), % 14
	(forall (x\ forall (y\ or (ng(is_snail x)) (or (ng(is_bird  y)) (much_smaller x y))))), % 15
	(forall (x\ forall (y\ or (ng(is_bird  x)) (or (ng(is_fox   y)) (much_smaller x y))))), % 16
	(forall (x\ forall (y\ or (ng(is_fox   x)) (or (ng(is_wolf  y)) (much_smaller x y))))), % 17
	(forall (x\ forall (y\ or (ng(is_wolf  x)) (or (ng(is_fox   y)) (ng(eats x y)))))), % 18
	(forall (x\ forall (y\ or (ng(is_wolf  x)) (or (ng(is_grain y)) (ng(eats x y)))))), % 19
	(forall (x\ forall (y\ or (ng(is_bird  x)) (or (ng(is_cater y)) (ng(eats x y)))))), % 20
	(forall (x\ forall (y\ or (ng(is_bird  x)) (or (ng(is_snail y)) (ng(eats x y)))))), % 21
	dummy, % 22
	(forall (x\ forall (y\ or (ng(is_cater x)) (or (ng(is_grain y)) (eats x y))))), % 23
	dummy, % 24
	(forall (x\ forall (y\ or (ng(is_snail x)) (or (ng(is_grain y)) (eats x y))))), % 25
	(forall (x\ forall (y\ forall (z\ or (ng(is_animal x)) (or (ng(is_animal y)) (or (ng(is_grain z)) (or (ng(eats x y)) (eats y z)))))))) % 26
]
[
	dummy, % 27
	dummy, % 28
	dummy, % 29
	dummy, % 30
	dummy, % 31
	dummy, % 32
	dummy, % 33
	dummy, % 34
	dummy, % 35
	dummy, % 36
	dummy, % 37
	dummy, % 38
	dummy, % 39
	dummy, % 40
	dummy, % 41
	dummy, % 42
	dummy, % 43
	dummy, % 44
	dummy, % 45
	dummy, % 46
	dummy, % 47
	dummy, % 48
	dummy, % 49
	dummy, % 50
	dummy, % 51
	dummy, % 52
	dummy, % 53
	dummy, % 54
	dummy, % 55
	dummy, % 56
	dummy, % 57
	dummy, % 58
	dummy, % 59
	dummy, % 60
	dummy, % 61
	dummy, % 62
	dummy, % 63
	dummy, % 64
	dummy, % 65
	dummy, % 66
	dummy, % 67
	dummy, % 68
	dummy, % 69
	dummy, % 70
	dummy, % 71
	dummy, % 72
	dummy, % 73
	dummy, % 74
	dummy, % 75
	dummy, % 76
	dummy, % 77
	dummy, % 78
	dummy, % 79
	dummy, % 80
	dummy, % 81
	dummy, % 82
	dummy, % 83
	dummy, % 84
	dummy, % 85
	dummy, % 86
	dummy, % 87
	dummy, % 88
	dummy, % 89
	dummy, % 90
	dummy, % 91
	dummy, % 92
	dummy, % 93
	dummy, % 94
	dummy, % 95
	dummy, % 96
	dummy, % 97
	dummy, % 98
	dummy, % 99
	dummy, % 100
	(ng(eats bi gi)), % 101
	(or (ng(eats fi bi)) (ng(eats bi gi))), % 102
	(or (ng(is_grain gi)) (or (ng(eats fi bi)) (ng(eats bi gi)))), % 103
	(or (ng (is_animal bi)) (or (ng(is_grain gi)) (or (ng(eats fi bi)) (eats bi gi)))), % 104
	dummy, % 105
	dummy, % 106
	dummy, % 107
	dummy, % 108
	dummy, % 109
	(is_animal fi), % 110
	dummy, % 111
	dummy, % 112
	dummy, % 113
	dummy, % 114
	dummy, % 115
	dummy, % 116
	dummy, % 117
	dummy, % 118
	dummy, % 119
	(is_animal bi), % 120
	dummy, % 121
	dummy, % 122
	dummy, % 123
	dummy, % 124
	dummy, % 125
	dummy, % 126
	dummy, % 127
	dummy, % 128
	dummy, % 129
	dummy, % 130
	dummy, % 131
	dummy, % 132
	dummy, % 133
	dummy, % 134
	dummy, % 135
	dummy, % 136
	dummy, % 137
	dummy, % 138
	dummy, % 139
	(ng(eats fi bi)), % 140
	(or (ng(eats bi gi)) (eats fi bi)), % 141
	(or (ng(much_smaller bi fi)) (or (ng(eats bi gi)) (eats fi bi))), % 142
	(or (eats fi gi) (or (ng(much_smaller bi fi)) (or (ng(eats bi gi)) (eats fi bi)))), % 143
	(or (ng(is_plant gi)) (or (eats fi gi) (or (ng(much_smaller bi fi)) (or (ng(eats bi gi)) (eats fi bi))))), % 144
	(or (ng(is_animal bi)) (or (ng(is_plant gi)) (or (eats fi gi) (or (ng(much_smaller bi fi)) (or (ng(eats bi gi)) (eats fi bi)))))), % 145
	(or (ng(is_plant gi)) (or (ng(is_animal bi)) (or (ng(is_plant gi)) (or (eats fi gi) (or (ng(much_smaller bi fi)) (or (ng(eats bi gi)) (eats fi bi))))))), % 146
	dummy, % 147
	dummy, % 148
	dummy, % 149
	(eats bi gi), % 150
	(or (eats bi gi) (eats bi si)), % 151
	(or (eats bi gi) (or (ng(eats si gi)) (eats bi si))), % 152
	(or (eats bi gi) (or (ng(much_smaller si bi)) (or (ng(eats si gi)) (eats bi si)))), % 153
	(or (ng(is_plant gi)) (or (eats bi gi) (or (ng(much_smaller si bi)) (or (ng(eats si gi)) (eats bi si))))), % 154
	(or (ng(is_animal si)) (or (ng(is_plant gi)) (or (eats bi gi) (or (ng(much_smaller si bi)) (or (ng(eats si gi)) (eats bi si)))))), % 155
	(or (ng(is_plant gi)) (or (ng(is_animal si)) (or (ng(is_plant gi)) (or (eats bi gi) (or (ng(much_smaller si bi)) (or (ng(eats si gi)) (eats bi si))))))), % 156
	dummy, % 157
	dummy, % 158
	dummy, % 159
	(is_plant gi), % 160
	dummy, % 161
	dummy, % 162
	dummy, % 163
	dummy, % 164
	dummy, % 165
	dummy, % 166
	dummy, % 167
	dummy, % 168
	dummy, % 169
	(ng(eats fi gi)), % 170
	(or (ng(eats fi gi)) (eats wi fi)), % 171
	(or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi))), % 172
	(or (eats wi gi) (or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi)))), % 173
	(or (ng(is_plant gi)) (or (eats wi gi) (or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi))))), % 174
	(or (ng(is_animal fi)) (or (ng(is_plant gi)) (or (eats wi gi) (or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi)))))), % 175
	(or (ng(is_plant gi)) (or (ng(is_animal fi)) (or (ng(is_plant gi)) (or (eats wi gi) (or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi))))))), % 176
	dummy, % 177
	dummy, % 178
	dummy, % 179
	(much_smaller bi fi), % 180
	(or (ng(is_fox   fi)) (much_smaller bi fi)), % 181
	dummy, % 182
	dummy, % 183
	dummy, % 184
	dummy, % 185
	dummy, % 186
	dummy, % 187
	dummy, % 188
	dummy, % 189
	(is_animal si), % 190
	dummy, % 191
	dummy, % 192
	dummy, % 193
	dummy, % 194
	dummy, % 195
	dummy, % 196
	dummy, % 197
	dummy, % 198
	dummy, % 199
	(much_smaller si bi), % 200
	(or (ng(is_bird  bi)) (much_smaller si bi)), % 201
	dummy, % 202
	dummy, % 203
	dummy, % 204
	dummy, % 205
	dummy, % 206
	dummy, % 207
	dummy, % 208
	dummy, % 209
	(eats si gi), % 210
	(or (ng(is_grain gi)) (eats si gi)), % 211
	dummy, % 212
	dummy, % 213
	dummy, % 214
	dummy, % 215
	dummy, % 216
	dummy, % 217
	dummy, % 218
	dummy, % 219
	(ng(eats bi si)), % 220
	(or (ng(is_snail si)) (ng(eats bi si))), % 221
	dummy, % 222
	dummy, % 223
	dummy, % 224
	dummy, % 225
	dummy, % 226
	dummy, % 227
	dummy, % 228
	dummy, % 229
	(is_animal wi), % 230
	dummy, % 231
	dummy, % 232
	dummy, % 233
	dummy, % 234
	dummy, % 235
	dummy, % 236
	dummy, % 237
	dummy, % 238
	dummy, % 239
	(ng(eats wi gi)), % 240
	(or (ng(is_grain gi)) (ng(eats wi gi))), % 241
	dummy, % 242
	dummy, % 243
	dummy, % 244
	dummy, % 245
	dummy, % 246
	dummy, % 247
	dummy, % 248
	dummy, % 249
	(much_smaller fi wi), % 250
	(or (ng(is_wolf  wi)) (much_smaller fi wi)), % 251
	dummy, % 252
	dummy, % 253
	dummy, % 254
	dummy, % 255
	dummy, % 256
	dummy, % 257
	dummy, % 258
	dummy, % 259
	(ng(eats wi fi)), % 260
	(or (ng(is_fox   fi)) (ng(eats wi fi))), % 261
	dummy, % 262
	dummy, % 263
	dummy, % 264
	dummy, % 265
	dummy, % 266
	dummy, % 267
	dummy, % 268
	dummy, % 269
	ff % 270 (previously 0)
]
% :%s/^\tresolv.*(idx\([^)]\+\).*(idx\([^)]\+\).* \([0-9]\+\),$/\tresol\1\2 \3,/gc
[
	resolveX 110 (res'   2 (rex'   7 done')),
	resolveX 120 (res'   3 (rex'   8 done')),
	resolveX 160 (res'  12 (rex'  11 done')),
	resolveX 190 (res'   5 (rex'  10 done')),
	resolveX 230 (res'   1 (rex'   6 done')),
	resolveX 261 (res'  18 (rex'   6 done')),
	resolveX 260 (res' 261 (rex'   7 done')),
	resolveX 251 (res'  17 (rex'   7 done')),
	resolveX 250 (res' 251 (rex'   6 done')),
	resolveX 241 (res'  19 (rex'   6 done')),
	resolveX 240 (res' 241 (rex'  11 done')),
	resolveX 221 (res'  21 (rex'  8 done')),
	resolveX 220 (res' 221 (rex'  10 done')),
	resolveX 211 (res'  25 (rex'  10 done')),
	resolveX 210 (res' 211 (rex'  11 done')),
	resolveX 201 (res'  15 (rex'  10 done')),
	resolveX 200 (res' 201 (rex'   8 done')),
	resolveX 181 (res'  16 (rex'   8 done')),
	resolveX 180 (res' 181 (rex'   7 done')),
	resolveX 176 (res'  13 (rex' 230 done')), % 
	resolveX 175 (res' 176 (rex' 160 done')),
	resolveX 174 (res' 175 (rex' 110 done')),
	resolveX 173 (res' 174 (rex' 160 done')),
	resolveX 172 (res' 173 (rex' 240 done')),
	resolveX 171 (res' 172 (rex' 250 done')),
	resolveX 170 (res' 171 (rex' 260 done')),
	resolveX 156 (res'  13 (rex' 120 done')),
	resolveX 155 (res' 156 (rex' 160 done')),
	resolveX 154 (res' 155 (rex' 190 done')),
	resolveX 153 (res' 154 (rex' 160 done')),
	resolveX 152 (res' 153 (rex' 200 done')),
	resolveX 151 (res' 152 (rex' 210 done')),
	resolveX 150 (res' 151 (rex' 220 done')),
	resolveX 146 (res'  13 (rex' 110 done')),
	resolveX 145 (res' 146 (rex' 160 done')),
	resolveX 144 (res' 145 (rex' 120 done')),
	resolveX 143 (res' 144 (rex' 160 done')),
	resolveX 142 (res' 143 (rex' 170 done')),
	resolveX 141 (res' 142 (rex' 180 done')),
	resolveX 140 (res' 141 (rex' 150 done')),
	resolveX 104 (res'  26 (rex' 110 done')),
	resolveX 103 (res' 104 (rex' 120 done')),
	resolveX 102 (res' 103 (rex'   7 done')),
	resolveX 101 (res' 102 (rex' 140 done')),
	resolveX 270 (res' 101 (rex' 150 done'))
].

example 201
[
	(forall (x\ forall (y\ forall (z\ forall (v\ 
         or (ng(is_animal x)) (or (ng(is_plant y)) 
        (or (ng(is_animal z)) (or (ng(is_plant v))
        (or (ng(eats x y)) (or (ng(much_smaller z x)) 
        (or (ng(eats z v)) (eats x z)))))))))))), % 13 -> 1
	(is_animal wi), % 230 -> 2
        ff              % 3
]
[
	(or (ng(is_plant gi)) (or (ng(is_animal fi)) (or (ng(is_plant gi)) (or (eats wi gi) (or (ng(much_smaller fi wi)) (or (ng(eats fi gi)) (eats wi fi))))))) % 176 -> 4
]
[
%	resolve' 4 (res' 2 (rex' 1 done'))
].

% A Prover9 translation example: SYN405+1
/*
1 -((all A f(A)) & (exists B g(B)) -> (exists C (f(C) & g(C)))).  [assumption].
2 -f(A) | -g(A).  [clausify(1)].
3 f(A).  [clausify(1)].
4 -g(A).  [resolve(2,a,3,a)].
5 g(c1).  [clausify(1)].
6 $F.  [resolve(4,a,5,a)].
*/
example 300 
  [(forall A\ or (ng (r A)) (ng (t A))), % 2 -> 1
   (forall A\ (r A)),                    % 3 -> 2
   (t m)]                                % 5 -> 3
  [(forall A\ (ng (t A))),               % 4 -> 4
   ff]                                   % 6 -> 5
  [resolve' 4 (res' 2 (rex' 1 done')),
   resolve' 5 (res' 3 (rex' 4 done'))].

% Another example, with factoring: SYN980+1
/*
1 -(all A ((all B ((r(A) -> r(B)) -> p(f(B),B))) -> (exists C exists B (p(C,B) & (q(f(A),A) -> q(C,B)))))).  [assumption].
2 -r(A) | p(f(A),A).  [clausify(1)].
3 r(c1) | p(f(A),A).  [clausify(1)].
4 -p(A,B) | q(f(c1),c1).  [clausify(1)].
5 -p(A,B) | -q(A,B).  [clausify(1)].
6 p(f(c1),c1) | p(f(A),A).  [resolve(2,a,3,a)].
7 -p(A,B) | -p(f(c1),c1).  [resolve(4,b,5,b)].
8 p(f(c1),c1).  [factor(6,a,b)].
9 -p(f(c1),c1).  [factor(7,a,b)].
10 $F.  [resolve(8,a,9,a)].
*/
% All clauses offset by one; r, p -> w, q, f -> s, c1 -> m
example 310
  [(forall A\           or (ng (r A))   (w (s A) A)),      % 1
   (forall A\           or (r m)        (w (s A) A)),      % 2
   (forall A\ forall B\ or (ng (w A B)) (q (s m) m)),      % 3
   (forall A\ forall B\ or (ng (w A B)) (ng (q A B)))]     % 4
  [(forall A\           or (w (s m) m)  (w (s A) A)),      % 5
   (forall A\ forall B\ or (ng (w A B)) (ng (w (s m) m))), % 6
   (w (s m) m),                                            % 7
   (ng (w (s m) m)),                                       % 8
   ff]                                                     % 9
  [resolve' 5 (res' 2 (rex' 1 done')),
   resolve' 6 (res' 3 (rex' 4 done')),
/* Reversing the positive - negative pair does not work.
  [resolve' 5 (res' 1 (rex' 2 done')),
   resolve' 6 (res' 4 (rex' 3 done')),
*/
   factor' 5 7,
   factor' 6 8,
   resolve' 9 (res' 7 (rex' 8 done'))].
