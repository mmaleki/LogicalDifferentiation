Inductive N:Set:= (*this is a comment line*)
|zero: N
|succ:N->N.

Fixpoint plus (m n:N):=
match m with
| zero=>n
|succ m'=>succ(plus m' n)
end.

Lemma zero_identity: forall n,n=plus n zero.
Proof.
induction n.
auto.
simpl.
f_equal.
assumption.
Qed.

