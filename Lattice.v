(* Definition and basic facts about distributive lattices. *)
Structure Lattice :={
  lt_carrier :> Type;
  lt_and : lt_carrier -> lt_carrier -> lt_carrier;
  lt_or : lt_carrier -> lt_carrier -> lt_carrier;
  lt_zero : lt_carrier;
  lt_one : lt_carrier;
  lt_and_commute : forall x y, lt_and x y = lt_and y x;
  lt_or_commute : forall x y, lt_or x y = lt_or y x;
  lt_and_associate : forall x y z, lt_and x (lt_and y z) = lt_and (lt_and x y) z;
  lt_or_associate : forall x y z, lt_or x (lt_or y z) = lt_or (lt_or x y) z;
  lt_or_absorb : forall x y, lt_or x (lt_and x y) = x;
  lt_and_absorb : forall x y, lt_and x (lt_or x y) = x;
  lt_zero_identity_r : forall x, lt_or x lt_zero = x;
  lt_one_identity_r : forall x, lt_and x lt_one = x;
  lt_distribute_or : forall x y z, lt_or x (lt_and y z) = lt_and (lt_or x y) (lt_or x z);
  lt_distribute_and : forall x y z, lt_and x (lt_or y z) = lt_or (lt_and x y) (lt_and x z)
}.

Hint Resolve lt_and_commute : lt_hints.
Hint Resolve lt_or_commute : lt_hints.
Hint Resolve lt_and_associate : lt_hints.
Hint Resolve lt_or_associate : lt_hints.
Hint Resolve lt_or_absorb : lt_hints.
Hint Resolve lt_and_absorb : lt_hints.
Hint Resolve lt_zero_identity_r : lt_hints.
Hint Resolve lt_one_identity_r : lt_hints.
Hint Resolve lt_distribute_or : lt_hints.
Hint Resolve lt_distribute_and : lt_hints.

Notation "p && q" := (lt_and _ p q) (at level 40, left associativity).
Notation "p || q" := (lt_or _ p q) (at level 50, left associativity).
Notation "1" := (lt_one _).
Notation "0" := (lt_zero _).

Structure LatticeHom (A B : Lattice) :=
  {
    lt_hom :> A -> B ;
    lt_hom_and : forall x y , lt_hom (x && y) = lt_hom x && lt_hom y;
    lt_hom_or : forall x y , lt_hom (x || y) = lt_hom x || lt_hom y;
    lt_hom_zero : lt_hom 0 = 0;
    lt_hom_one : lt_hom 1 = 1
  }.

Definition lt_id {A : Lattice}: LatticeHom A A.
Proof.
  refine {| lt_hom := fun x => x |} ; reflexivity.
Defined.

Definition lt_comp {A B C:Lattice}: LatticeHom B C -> LatticeHom A B -> LatticeHom A C.
Proof.
  intros g f.
  refine {| lt_hom := fun x => g (f x) |}.
  - intros. rewrite lt_hom_and. rewrite lt_hom_and. reflexivity.
  - intros; repeat (rewrite lt_hom_or). reflexivity.
  - intros. repeat (rewrite lt_hom_zero). reflexivity.
  - intros. repeat (rewrite lt_hom_one). reflexivity.
Defined.

Notation "g 'o' f" := (lt_comp g f) (at level 65, left associativity).

Lemma lt_id_left (A B : Lattice) (f : LatticeHom A B) (x: A): (lt_id o f) x  = f x.
Proof.
  reflexivity.
Qed.

Lemma comp_assoc
      (A B C D : Lattice)
      (f : LatticeHom A B)
      (g : LatticeHom B C) (h : LatticeHom C D) (x : A) :
  (h o (g o f)) x = ((h o g) o f) x.
Proof.
  reflexivity.
Qed.
