Require Import QArith.

Print Q.

Print Qnum.
Print Qden.

Check Qnum.

Definition inj (z :Z):= Qmake z 1.

 Eval compute in (inj 3).

Eval compute in ( (3 # 5) * (4# 6)).

Eval compute in ((2#3)+(4#8)).



Definition interval (p q :Q):={x : Q| p < x /\ x< q}.
Definition interval_empty(p : Q):={x :Q | p < x /\ x< p}.

Lemma interval_meet(p q r s :Q): q<r-> (interval_empty p).

 
 