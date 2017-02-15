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

(* Every Boolean algebra is a poset. *)
Definition BAPoset (B : BooleanAlgebra) : Poset.
Proof.
  refine {| poset_carrier := carrier B ;
            leq := fun x y => (x & y = x)
         |}.
  - admit.
  - admit.
  - admit.
Admitted.
