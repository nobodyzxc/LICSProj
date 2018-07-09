% scheme evaluator
% define syntax supports top level eval only.
% and nest define is also not supported
% test data is at the EOF
% special form impl : define(top eval-lv only),
%                     if,
%                     lambda, let(lambda's sugar)

:- nb_setval(global, [
    [=, eqv],
    [<, lt],
    [>, gt],
    [+, add],
    [-, sub],
    [car, car],
    [cdr, cdr],
    [cons, cons],
    [list, list],
    [null, null]
    ]).

% ev with global
ev(Expr, Val) :-
    nb_getval(global, Global),
    (Expr = [define | Body] ->
        define(Global, Body);
    eval(Global, Expr, Val)), !.

% eval atom
eval(Env, Expr, Val) :-
    assoc(Env),
    atomic(Expr),
    (number(Expr) -> Val = Expr, !;
        string(Expr) -> Val = Expr, !;
        boolean(Expr) -> Val = Expr, !;
        is_list(Expr) -> Val = Expr, !;
        lookup(Env, Expr, Val)).

% eval compound
eval(Env, Expr, Val) :-
    assoc(Env),
    Expr = [F|A],
    (F == if -> if(Env, A, Val);
     F == lambda ->
        [Args | Exprs] = A,
        lambda(Env, Args, Exprs, Val);
     F == let ->
        [Binds | Exprs] = A,
        let(Env, Binds, Exprs, Val);
    eval(Env, F, App),
    maplist(eval(Env), A, Args),
    apply(Env, App, Args, Val)).

% eval if
if(Env, [Cond, Then, Else], Val) :-
    (eval(Env, Cond, true) ->
        eval(Env, Then, Val);
        eval(Env, Else, Val)).

% eval define
define(Env, [Hs | Exprs]) :-
    (is_list(Hs) ->
        [Fn | Args] = Hs,
        lambda(Env, Args, Exprs, Lambda),
        nb_setval(global, [[Fn, Lambda] | Env]);
    [Expr] = Exprs,
    eval(Env, Expr, Val),
    nb_setval(global, [[Hs, Val] | Env])).

% eval let
head([X|_], X).
secd([_,X], X).
tail([_|T], T).
let(Env, Binds, Exprs, Val) :-
    maplist(head, Binds, BindPars),
    maplist(secd, Binds, BindArgs),
    lambda(Env, BindPars, Exprs, Lambda),
    maplist(eval(Env), BindArgs, Args),
    apply(Env, Lambda, Args, Val).


% apply lambda
eval_seq(Env, [Expr], Val) :-
    eval(Env, Expr, Val).

eval_seq(Env, [Expr | Exprs], Val) :-
    eval(Env, Expr, _),
    eval_seq(Env, Exprs, Val).

apply(Env, App, Args, Val) :-
    assoc(Env),
    lambda(Closure, Paras, Exprs) = App,
    (is_list(Paras) ->
        extenv(Paras, Args, Closure, Ext), %clos
        eval_seq(Ext, Exprs, Val);
     Ext = [[Paras, Args] | Closure], %clos
     eval_seq(Ext, Exprs, Val)).

% apply build-ins
apply(Env, App, Args, Val) :-
    assoc(Env),
    atomic(App),
    apply(App, [Args, Val]).

% data structure
boolean(B) :-
    B == true;
    B == false.

lambda(Env, _, Exprs) :-
    assoc(Env),
    is_list(Exprs).

lambda(Env, Paras, Exprs, Val) :-
    is_list(Exprs),
    Exprs \= [],
    Val = lambda(Env, Paras, Exprs), !.

assoc([]).
assoc([[_,_] | A]) :-
    assoc(A).

% zip eq length list only
zip([], [], []).
zip([X|Xs], [Y|Ys], Z) :-
    zip(Xs, Ys, N),
    Z = [[X,Y] | N].

extenv(Para, Args, Env, Ext) :-
    zip(Para, Args, Pa),
    append(Pa, Env, Ext).

assoc([], _, Val) :-
    Val = error, !.
% fail. the bug QAQ

assoc(Lst, Key, Val) :-
    [[K, V] | Rest] = Lst,
    (Key == K ->
        Val = V;
        assoc(Rest, Key, Val)).

lookup(Lst, Key, Val) :-
    assoc(Lst, Key, VfromEnv),
    (VfromEnv = error ->
        nb_getval(global, Global),
        assoc(Global, Key, VfromGlo),
        (VfromGlo = error ->
            write("cannot find "),
            writeln(Key),
            Val = error, fail;
            Val = VfromGlo);
        Val = VfromEnv).

% build-ins
eqv([A,B], V) :-
    (A == B -> V = true; V = false).

lt([A, B], V) :-
    (A < B -> V = true; V = false).

gt([A, B], V) :-
    (A > B -> V = true; V = false).

add([], 0).
add([D|R], Val) :-
    add(R, S),
    Val is D + S.

sub([], 0).
sub([D|R], Val) :-
    sub(R, S),
    Val is D - S.

list(L, L) :-
    is_list(L).

car([[X|_]], X).
cdr([[_|Xs]], Xs).
cons([E,Lst], [E|Lst]).

null([[]], true).
null([[_|_]], false).

:- ev([define, [succ, x], [+, x, 1]],_).

% test for let
/*

?- ev([let, [[x,1], [y, [+, 3, 4]]], [-, y , x]], V).
V = 6.

*/

% test for define var
:- ev([define, x, 1], _).
/*

?- ev(x, V).
V = 1.

*/

% test for define func in short form
:- ev([define, [add, x, y], [+, x, y]], _).

/*

?- ev([add, 1, 2], V).
V = 3.

*/

% test for define recursive func
:- ev([define , [fib, x],
  [if, [<, x, 2], x,
      [+, [fib , [-, x, 1]], [fib, [-, x, 2]]]
     ]], _).

/*

?- ev([fib, 7], V).
V = 13.

*/

% test for define higher order func
:- ev([define ,
  [foldl, func, base, lst],
  [if, [null, lst], base,
      [foldl, func, [func, [car, lst], base], [cdr, lst]]]], _).
:- ev([define, sum, [lambda, args, [foldl, +, 0, args]]], _).
/*

?- ev([sum, 1, 2, 3, 4], V).
V = 10.

*/

:- ev([define ,
  [foldr, func, base, lst],
  [if, [null, lst], base,
      [func, [car, lst], [foldr, func, base, [cdr, lst]]]]], _).

% test for define func in lambda form
:- ev([define, [map, func, lst],
    [foldr, [lambda, [e, acc], [cons, [func, e], acc]], [], lst]], _).

/*

?- ev([foldr, cons, [], [list, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]], V).
V = [0, 1, 2, 3, 4, 5, 6, 7, 8|...].

?- ev([foldl, cons, [], [list, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]], V).
V = [9, 8, 7, 6, 5, 4, 3, 2, 1|...].

?- ev([map, fib, [list, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]], V).
V = [0, 1, 1, 2, 3, 5, 8, 13, 21|...].

*/

