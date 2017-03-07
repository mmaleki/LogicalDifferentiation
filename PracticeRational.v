Require Import QArith.

Print Q.

Print Qnum.
Print Qden.

Check Qnum.

Definition inj (z :Z):= Qmake z 1.

 Eval compute in (inj 3).

Eval compute in ( (3 # 5) * (4# 6)).

Eval compute in ((2#3)+(4#8)).

Check transitivity.

Check Qlt.
Check Qlt_le_trans.
Check Qlt_le_weak.

Definition interval (p q :Q):={x : Q| p < x /\ x< q}.
Definition interval_empty(p : Q):={x :Q | p < x /\ x< p}.

Lemma ref:forall p q r :Q,p < q /\ q < r -> p < r.
Proof.
intros.
destruct H.
apply (Qlt_le_trans p q r).
apply H.
apply Qlt_le_weak.
apply H0.
Defined.

