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

p(N).

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
satisfies(V, F) 			:- list_members(V, F).

satisfies(V, neg(X))		:- neg(satisfies(V, X)).

satisfies(V, and(X, Y)) 	:- and(satisfies(V, X), satisfies(V, Y)).

satisfies(V, or(X, Y))		:- or(satisfies(V, X), satisfies(V, Y)).

satisfies(V, impl(X, Y))	:- impl(satisfies(V, X), satisfies(V, Y)).

satisfies(V, xor(X, Y))		:- xor(satisfies(V, X), satisfies(V, Y)).

satisfies(V, equiv(X, Y))	:- equiv(satisfies(V, X), satisfies(V, Y)).


list_members([X|_], p(X)).

list_members([_|T], p(X)) 	:- list_members(T, p(X)).

/*
* find_val_tt/2
*/

%find_val_tt(F, V)			:- 	append([], F, V).

find_val_tt(p(F), V)		:- 	append(F,[],V).

find_val_tt(and(X, Y), V)	:- 	append(find_val_tt(X, V), [], V),
								append(find_val_tt(Y, V), [], V).


add2end(X,[H|T],[H|NewT]):-add2end(X,T,NewT).
add2end(X,[],[X]).
