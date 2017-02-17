Structure Lattice :={
  lattice_carrier :> Type;
  lattice_and : lattice_carrier -> lattice_carrier -> lattice_carrier;
  lattice_or : lattice_carrier -> lattice_carrier -> lattice_carrier;
  lattice_zero : lattice_carrier;
  lattice_one : lattice_carrier;
  and_comut : forall x y, lattice_and x y = lattice_and y x;
  or_comut : forall x y, lattice_or x y = lattice_or y x;
  and_assoc : forall x y z, lattice_and x ( lattice_and y z)
   = lattice_and (lattice_and x y) z;
  or_assoc : forall x y z, lattice_or x ( lattice_or y z)
   = lattice_or (lattice_or x y) z;
  absorb_or : forall x y, lattice_or x (lattice_and x y)=x;
  absorb_and : forall x y, lattice_and x (lattice_or x y)=x;
  zero_identity : forall x, lattice_or x lattice_zero = x;
  one_identity : forall x, lattice_and x lattice_one = x;
  distrib_or_and : forall x y z, lattice_or x (lattice_and y z)
  = lattice_and (lattice_or x y) (lattice_or x z);
  distrib_and_or : forall x y z, lattice_and x (lattice_or y z)
  = lattice_or (lattice_and x y) (lattice_and x z)
}.

Notation "p & q" := (lattice_and _ p q) (at level 40, left associativity).
Notation "p | q" := (lattice_or _ p q) (at level 50, left associativity).
Notation "1" := (lattice_zero _).
Notation "0" := (lattice_zero _).

Lemma firstt(B: Lattice) :  1 & 1 = 1.

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
