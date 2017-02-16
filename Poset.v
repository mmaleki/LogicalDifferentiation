Require Import BooleanAlgebra.

Structure Poset := {
  poset_carrier :> Type;
  leq : poset_carrier -> poset_carrier -> Prop ;
  leq_refl : forall x, leq x x ;
  leq_tran : forall x y z, leq x y -> leq y z -> leq x z;
  leq_antisym : forall x y, leq x y -> leq y x -> x = y
}.

Notation "x <= y" := (leq _ x y) (at level 70, no associativity).

Definition discrete (A : Type) : Poset.
Proof.
  refine {| poset_carrier := A ; leq := (fun x y => x = y) |}.
  - auto.
  - intros. transitivity y ; auto.
  - intros. assumption.
Defined.

Lemma assosfour {B:BooleanAlgebra}(y z:B):
y & z & z= y & z.
Proof.
rewrite<-and_p_qr.
rewrite ->and_p_p.
trivial.
Qed.

(* Every Boolean algebra is a poset. *)
Definition BAPoset (B : BooleanAlgebra) : Poset.
Proof.
  refine {| poset_carrier := carrier B ;
            leq := fun x y => (x & y = x)
         |}.
  -intros. apply and_p_p.
  -intros.
   rewrite <- H.
   rewrite <- and_p_qr.
   rewrite -> H0.
   trivial.
  -intros. rewrite <- H. rewrite and_pq. assumption.
Qed.
