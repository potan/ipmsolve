
ap(A -> B, A, B).

axiom(A -> (_ -> A), "A->B->A").
axiom((A -> (B -> C)) -> ((A -> B) -> (A -> C)), "(A->B->C)->(A->B)->A->C").
axiom((~(A) -> ~(B)) -> (B -> A), "(~A->B)->(B->A)").
axiom(A) :- axiom(A, _).

nsplit(1, 0, 0).
nsplit(N, X, Y) :- N > 1,
                   P is N-1,
                   nsplit(P, XO, YO),
                   (
                     X is XO+1, Y = YO ;
                     X = XO, Y is YO+1
                   ).

solve(P, C, C, _, A, A) :- member(P, C), !.
solve(P, C, [P|C], _, A, A) :- axiom(P).
solve(P, C, T, N, Aps, [X | Apso]) :- N > 0,
                     ap(X, Y, P),
%                      nsplit(N, A, B),
                     A is N-1, B = A,
                     solve(X, C, TA, A, [], Aps1),
                     acyclic_term(X),
                     solve(Y, TA, TB, B, [], Aps2),
                     append([Aps2, Aps1, Aps], Apso),
                     T = [P | TB].


marks([], [], _).
marks([V|T], [(N,V)|TM], N) :- N1 is N+1, marks(T, TM, N1).
marks(I, O) :- marks(I, O, 0).

get(N, F, L) :- member((N, (_ -> F)), L), !.
get(N, F, _) :- axiom(F, N), !.
get(F, F, _).

show([], _).
show([(N, (A -> B)) | T], L) :- get(NA, A, L),
                           get(NF, (A -> B), L),
                           writeln((N=NF^NA, (A -> B))),
                           show(T).
show(L) :- show(L, L).

run(P, N, R, A) :- solve(P, [], R, N, [], A), acyclic_term(R).
run(P, N, L) :- run(P, N, _, A),
             marks(A, AM),
             length(AM, L),
             show(AM).

% run((a -> (b -> c)) -> (b -> (a -> c)), 6, L).
% run((~(a) -> a) -> a, 6, L).
