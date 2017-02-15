Structure Poset :=
{ carrier :> Type;
  leq : carrier -> carrier -> Prop ;
  leq_refl : forall x, leq x x ;
  leq_tran : forall x y z, leq x y -> leq y z -> leq x z;
  leq_antisym : forall x y, leq x y -> leq y x -> x = y
}.

Definition discrete (A : Type) : Poset.
Proof.
  refine {| carrier := A ; leq := (fun x y => x = y) |}.
- auto.
- intros. transitivity y ; auto.
- intros. assumption. 
Defined.

Print discrete.
