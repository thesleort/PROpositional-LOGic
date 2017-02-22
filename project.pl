/*
 *
 *	Troels Blicher Petersen (trpet15)
 *	22 February 2017
 *	Prolog project.
 *
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

wff(p(X))			:-  X.

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

find_val(p(F), V)		:- 	list_init(F, V).

find_val(neg(X), V)		:- 	find_val(X, A),
							zip([], [A], V).

find_val(and(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							zip([A], [B], V).

find_val(or(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							zip([A], [B], V).
							
find_val(impl(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							zip([A], [B], V).

find_val(xor(X, Y), V)	:- 	find_val(X, A),
							find_val(Y, B),
							zip([A], [B], V).

find_val(equiv(X, Y), V):- 	find_val(X, A),
							find_val(Y, B),
							zip([A], [B], V).

/* 
 *taut_tt/1 sat_tt/1 unsat_tt/1
 */

taut_tt(F)	:-	unsat_tt(neg(F)).

sat_tt(F)	:-	find_val_tt(F, V).

unsat_tt(F)	:-	neg(sat_tt(F)).

/*
 * tableu/2
 */

tableau(p(F), [p(F)]).

tableau(neg(p(F)), [neg(p(F))]).

tableau(neg(neg(p(F))), V)	:-	tableau(N,V)

%AND
tableau(and(X, Y), V)		:-	tableau(X, A),
								tableau(Y, B),
								zip(A, B, V).
						
tableau(neg(and(X,_)), V)	:-	tableau(neg(X), V).

tableau(neg(and(_,X)), V)	:-	tableau(neg(X), V).

%OR
tableau(or(X,_), V)			:-	tableau(X, V).

tableau(or(_,X), V)			:-	tableau(X, V).

tableau(neg(or(X, Y)), V)	:-	tableau(neg(X), A),
								tableau(neg(Y), B),
								zip(A, B, V).

%IMPLICATION
tableau(impl(X,_), V)		:-	tableau(neg(X), V).

tableau(impl(_,X), V)		:-	tableau(X, V).

tableau(neg(impl(X, Y)), V)	:-	tableau(X, A),
								tableau(neg(Y), B),
								zip(A, B, V).

%EQUIVALENT
tableau(equiv(X, Y), V)		:-	tableau(X, A),
								tableau(Y, B),
								zip(A, B, V).

tableau(equiv(X, Y), V)		:-	tableau(neg(X), A),
								tableau(neg(Y), B),
								zip(A, B, V).
							
tableau(neg(equiv(X, Y)), V):-	tableau(X, A),
								tableau(neg(Y), B),
								zip(A, B, V).

tableau(neg(equiv(X, Y)), V):-	tableau(neg(X), A),
								tableau(Y, B),
								zip(A, B, V).

%EXCLUSIVE OR
tableau(xor(X, Y), V)		:-	tableau(X, A),
								tableau(neg(Y), B),
								zip(A, B, V).

tableau(xor(X, Y), V)		:-	tableau(neg(X), A),
								tableau(Y, B),
								zip(A, B, V).

tableau(neg(xor(X, Y)), V)	:-	tableau(neg(X), A),
								tableau(Y, B),
								zip(A, B, V).

/*
 * find_val_tab/2
 */
find_val_tab(F, V)	:-	tableau(F, X),
						getnumbers(X, V),
						satisfies(V,F).

/*
 * taut_tab/1 sat_tab/1 unsat_tab/1
 */
taut_tab(F)	:-	unsat_tab(neg(F)).

sat_tab(F)	:-	find_val_tab(F, V).

unsat_tab(F):-	neg(sat_tab(F)).

/*
 * Tool predicates
 */
permutations([], []).
permutations([X|Y], [X|Z])		:-	permutations(Y, Z).
permutations([_|Y], Z)			:-	permutations(Y, Z).

list_init(X, X).

getnumbers([], []).
getnumbers([p(K)|V], [K|Vtail]) :- getnumbers(K, Vtail).
getnumbers([_|V],Vtail) 		:- getnumbers(V, Vtail).

zip([], [], []).

zip([], [Y|Ynext], [Y|Znext])			:-	zip([], Ynext, Znext).

zip([X|Xnext], [Y|Ynext], [X,Y|Znext])	:-	zip(Xnext,Ynext,Znext).
