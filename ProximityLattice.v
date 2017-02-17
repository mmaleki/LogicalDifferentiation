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
Notation "1" := (lattice_one _).
Notation "0" := (lattice_zero _).

Structure lattice_morphism ( A B : Lattice):={
l_mor:> A ->B;
l_mor_and : forall x y , l_mor ( x & y) = l_mor x & l_mor y;
l_mor_or : forall x y , l_mor (x | y) = l_mor x | l_mor y;
l_mor_zero : l_mor 0 = 0;
l_mor_one : l_mor 1 = 1
}.


Definition id_morphism{A : Lattice}: lattice_morphism A A.
Proof.
refine {| l_mor := fun x => x |};reflexivity.
Defined.

Definition comp {A B C:Lattice}: lattice_morphism B C->lattice_morphism A B -> lattice_morphism A C.
Proof.
intros g f.
 refine {| l_mor := fun x => g (f x) |}.
-intros. rewrite l_mor_and. rewrite l_mor_and. reflexivity.
-intros; repeat (rewrite l_mor_or). reflexivity.
-intros. repeat (rewrite l_mor_zero). reflexivity.
-intros. repeat (rewrite l_mor_one). reflexivity.
Defined.

Notation " g 'o' f" := (comp g f) (at level 65, left associativity).

Lemma id_o(A B : Lattice) (f : lattice_morphism A B) (x :A):  (id_morphism o f) x = f x.
Proof.
Admitted.

Lemma assos_l (A B C D : Lattice)(f : lattice_morphism A B) (g : lattice_morphism B C) (h : lattice_morphism C D): h o (g o f) = (h o g) o f.
Proof.
Admitted. 




