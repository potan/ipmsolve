ap(A -> B, A, B).

axiom(hilbert_pos, A -> (_ -> A), "A->B->A").
axiom(hilbert_pos, (A -> (B -> C)) -> ((A -> 😎 -> (A -> C)), "(A->B->C)->(A->B)->A->C").
axiom(hilbert, (~(A) -> ~(B)) -> (B -> A), "(~A->~B)->(B->A)").

axiom(hilbert_hlp, (B -> C) -> ((A -> 😎 -> (A -> C)), "(B->C)->((A->B)->(A->C))").
axiom(hilbert_hlp, (A -> (B -> C)) -> (B -> (A -> C)), "(A->(B->C))->(B->(A->C))").
axiom(hilbert_hlp, (~(A)) -> (A -> _), "~A->(A->B)").
axiom(hilbert_hlp, ((~(A)) -> A) -> A, "(~A->A)->A)").
axiom(hilbert_hlp, (~(~(A))) -> A, "~~A->A").
axiom(hilbert_hlp, A -> (~(~(A))), "A->~~A").

axiom(Theories, A) :- axiom(Theory, A, _), member(Theory, Theories).

nsplit(1, 0, 0).
nsplit(N, X, Y) :- N > 1,
                   P is N-1,
                   nsplit(P, XO, YO),
                   (
                     X is XO+1, Y = YO ;
                     X = XO, Y is YO+1
                   ).

solve(Theories, P, C, [P|C], _, A, A) :- axiom(Theories, P).
% solve(_, P, C, C, _, A, A) :- member(P, C).
solve(Theories, P, C, T, N, Aps, [X | Apso]) :- N > 0,
                     ap(X, Y, P),
%                      nsplit(N, A, B),
                     A is N-1, B = A,
                     solve(Theories, X, C, TA, A, [], Aps1),
                     solve(Theories, Y, TA, TB, B, [], Aps2),
                     acyclic_term(X),
                     append([Aps2, Aps1, Aps], Apso),
                     T = [P | TB].


marks([], [], _).
marks([V|T], [(N,V)|TM], N) :- N1 is N+1, marks(T, TM, N1).
marks(I, O) :- marks(I, O, 0).

get(N, F, L) :- member((N, (_ -> F)), L), !.
get(N, F, _) :- axiom(_, F, N), !.
get(F, F, _).

show([], _).
show([(N, (A -> B)) | T], L) :- get(NA, A, L),
                           get(NF, (A -> B), L),
                           writeln((N=NF^NA, (A -> B))),
                           show(T).
show(L) :- show(L, L).

run(Theories, P, N, R, A) :- solve(Theories, P, [], R, N, [], A)
                   , acyclic_term(R)
                   .
run(Theories, P, N, L) :- run(Theories, P, N, _, A),
             marks(A, AM),
             length(AM, L),
             show(AM).

% run([hilbert_pos], (a -> (b -> c)) -> (b -> (a -> c)), 6, L).
% run([hilbert_pos, hilbert], (~(a) -> a) -> a, 5, L).
% run([hilbert_pos, hilbert, hilbert_hlp], (a -> b) -> ((~(a) -> b) -> b), 4, L).
% run([hilbert_pos, hilbert, hilbert_hlp], (b -> a) -> (~(a) -> ~(b)), 4, L).
