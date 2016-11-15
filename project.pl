/*
No: 
so no ;, -> and ^ = you'll fail
Disjunction
implication
existential quantifier
If you use these things he'll chop your head off.
*
*	Troels Blicher Petersen(trpet15)
*	12:49 Monday the 7th of November 2016
*	Prolog project.
*
*/
%problem 1:
%Define a predicate wff/1 that checks whether its argument is a propositional formula (wff standsfor well-formed formula).
% well formed impl(equiv(p(1),p(2)),and(p(3),or(p(1),neg(p(3))))).
/*
* Check for impl(*,*)
* check for p(int) basecase
* check for neg(*,*)
* check for and(*,*)
* check for equiv(*,*)
* check for xor(*,*)
*/

p(K).

neg(X)      :-  \+X.

and(X, Y)   :-  X, Y.

or(X, Y) 	:- 	neg(and(neg(and(X, X)), neg(and(Y, Y)))).

impl(X, Y)  :-  or(neg(X), Y).

xor(X, Y)   :- 	or(X, Y), neg(and(X, Y)).

equiv(X, Y) :-  or(and(X, Y), and(neg(X), neg(Y))).

/*
* Well-formed formula
*/

wff(X)			:-  X.

wff(neg(X))		:-	wff(X).

wff(and(X, Y))	:-	wff(X),
					wff(Y).

wff(or(X, Y))	:-	wff(X),
					wff(Y).

wff(impl(X, Y)) :- 	wff(X),
					wff(Y).

wff(xor(X, Y))	:-	wff(X),
					wff(Y).

wff(equiv(X, Y)):-	wff(X),
					wff(Y).



/*
* satisfies/2
*
* satisfies([1],neg(1)).
* satisfies([1],neg(2)).
*/
satisfies(V, p(F)) 			:- list_contains(V, F).

satisfies(V, neg(X))		:- neg(satisfies(V, X)).

satisfies(V, and(X, Y)) 	:- and(satisfies(V, X), satisfies(V, Y)).

satisfies(V, or(X, Y))		:- or(satisfies(V, X), satisfies(V, Y)).

satisfies(V, impl(X, Y))	:- impl(satisfies(V, X), satisfies(V, Y)).

satisfies(V, xor(X, Y))		:- xor(satisfies(V, X), satisfies(V, Y)).

satisfies(V, equiv(X, Y))	:- equiv(satisfies(V, X), satisfies(V, Y)).


list_contains([X|_], X).

list_contains([_|T], X) 	:- list_contains(T, X).

/*
* find_val_tt/2
*/

find_val_tt(F, V)		:-	find_val(F, A),
							flatten(A, B),
							sort(B, C),
							permutations(C, V),
							satisfies(V, F).

find_val(p(F), V)		:- 	append([], F, V).

find_val(neg(X), V)		:- 	find_val(X, A),
							append([], A, V).

find_val(and(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							append([A], [B], V).

find_val(or(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							append([A], [B], V).
							
find_val(impl(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							append([A], [B], V).

find_val(xor(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							append([A], [B], V).

find_val(equiv(X, Y), V):- 	find_val(X, A),
							find_val(Y, B),
							append([A], [B], V).

sublist(L, S) 			:-	length(L, N),
							between(1, N, M),
							length(S, M),
							append([_,S,_], L).


permutations([], []).
permutations([X|Y], [X|Z])		:-	permutations(Y, Z).
permutations([_|Y], Z)			:-	permutations(Y, Z).

zip([], [], []).
zip([X|Xnext], [Y|Ynext], [X,Y|Znext]) :- zip(Xnext,Ynext,Znext).
/*
permutation(L, S)		:-	split(L, _, A),
    						%SubList = [_|_],      disallow empty list 
    						permute(A, S).

split([ ], [ ], [ ]).

split([H|T], [H|L], R)	:-	split(T, L, R).

split([H|T], L, [H|R])	:-	split(T, L, R).

permute([ ], [ ]) 		:-	!.

permute(L, [X|R]) 		:-	omit(X, L, M),
    						permute(M, R).

omit(H, [H|T], T).

omit(X, [H|L], [H|R]) 	:-	omit(X, L, R).
*/

/*
* taut_tt/1 sat_tt/1 unsat_tt/1
taut_tt(or(or(p(2),neg(p(3))),p(1))).
taut_tt(or(p(1),neg(p(1)))).

impl(equiv(p(1),p(2)),and(p(3),or(p(1),neg(p(3)))))
*/

taut_tt(F)	:-	unsat_tt(neg(F)).

sat_tt(F)	:-	find_val_tt(F, V).

unsat_tt(F)	:-	neg(sat_tt(F)).

/*
* tableu/2
tableu(and(p(1),p(1)),V).

tableu(F, V)	:- get_leaf(F, V, true).
							
tableau(impl(equiv(p(1),p(2)),and(p(3),or(p(1),neg(p(3))))),V).							
							*/
tableau(F, V)				:-	get_leaf(F, V).



get_leaf(p(F), V)			:-	append([],p(F), V).

get_leaf(neg(p(F)), V)		:-	append([],neg(p(F)),V).

get_leaf(neg(neg(p(F))),V)	:-	append([],p(F),V).

%AND get_leaf(or(p(1),and(p(1),p(2))),V).
% get_leaf(and(p(1),p(2)),V).
get_leaf(and(X, Y), V)		:-	get_leaf(X, A),
								get_leaf(Y, B),
								append([A],[B],V).
/*
get_leaf(neg(and(X, Y)), V)	:-	get_leaf(neg(X), A),
								get_leaf(neg(Y), B).
								append([A], B, V).
*/
%OR
get_leaf(or(X,_), V)		:-	get_leaf(X, V).

get_leaf(or(_,X), V)		:-	get_leaf(X, V).
								
								%append([A], [B], V).
/*
get_leaf(neg(or(X, Y)), V)	:-	get_leaf(neg(X), A),
								get_leaf(neg(Y), B).
								%append([A], [B], V).

%IMPLICATION tableau(or(p(1),p(2)),V).
get_leaf(impl(X, Y), V)		:-	get_leaf(neg(X), A),
								get_leaf(Y, B).
								%append([A], [B], V).

get_leaf(neg(impl(X, Y)), V):-	get_leaf(X, A),
								get_leaf(neg(Y), B).
								%append([A], [B], V).

%EXCLUSIVE OR
get_leaf(xor(X, Y), V)		:-	get_leaf(X, A),
								get_leaf(neg(Y), B),
								get_leaf(neg(X), C),
								get_leaf(Y, D).
								%append([A, B], [C, D], V).

get_leaf(neg(xor(X, Y)), V)	:-	get_leaf(X, A),
								get_leaf(Y, B),
								get_leaf(neg(X), C),
								get_leaf(neg(Y), D).
								%append([A, B], [C, D], V).

%EQUIVALENT
get_leaf(equiv(X, Y), V)		:-	get_leaf(and(X, Y), A),
									get_leaf(neg(and(X, Y), B).
									%append([A], [B], V).

get_leaf(neg(equiv(X, Y)), V)	:-	get_leaf(neg(impl(X, Y)), A),
									get_leaf(impl(X, Y), B).
									%append([A], [B], V).