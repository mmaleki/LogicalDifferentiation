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

Lemma id_o(A B : Lattice) (f : lattice_morphism A B) (x: A):  (id_morphism o f) x  = f x.
Proof.
reflexivity.
Qed.

Lemma assos_l (A B C D : Lattice)(f : lattice_morphism A B)
(g : lattice_morphism B C) (h : lattice_morphism C D) (x : A):
(h o (g o f)) x = ((h o g) o f) x.
Proof.
reflexivity.
Qed.

Structure ProximityLattice :={
p_lattice :> Lattice;
p_approx : p_lattice  -> p_lattice  -> Prop;
o_1r : forall x y z , p_approx x z /\ p_approx y z -> p_approx (x | y) z;
o_1ll : forall x y z, p_approx (x | y) z -> p_approx x z;
o_1lr : forall x y z, p_approx (x | y) z -> (p_approx y z /\ p_approx y z);
o_2 : forall x , x <> 1 -> p_approx x 1;
o_3 : forall x y z , p_approx x y /\ p_approx x z <-> p_approx x (y & z);
o_4 : forall x y z , p_approx x (y | z) -> (exists y' z' , p_approx y' y
      /\ p_approx z' z /\ p_approx x (y' | z'));
o_trans : forall x y z, p_approx x y /\ p_approx y z -> p_approx x z;
o_inter : forall x y, p_approx x y -> (exists z, p_approx x z /\ p_approx z y)
}.

Notation "x << y" := (p_approx _ x y)(at level 70, no associativity).

Structure ApproximableMapping (A B : ProximityLattice) :={
  relation : A -> B -> Prop;
  relation_m1 : forall x y , relation x y -> (exists z, x<< z /\ relation z y);
  relation_m2 : forall x y , relation x y -> (exists z, z<< y /\ relation x z);
  relation_m3left : forall x y z , ( relation x z /\ relation y z ) -> relation ( x | y) z;
  relation_m3right : forall x y z , relation (x | y) z -> ( relation x z /\ relation y z );
  relation_m4 : forall x, x << 1 -> relation x 1;
  relation_m5left : forall x y z , ( relation x y /\ relation x z) -> relation x (y & z);
  relation_m5right : forall x y z , relation x ( y & z) -> (relation x y /\ relation x z);
  relation_m6 : forall x y z , relation x ( y | z) -> (exists N , x << N /\ exists m, relation N m)
}.

Definition id_approx {A : ProximityLattice} : ApproximableMapping A A.
Proof.
refine {| relation := fun x y => x << y|}.
- intros. 
admit.
-admit.
-admit.
-intros. rewrite ->(o_1ll A x y z).


