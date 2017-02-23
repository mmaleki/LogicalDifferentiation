Require Import List.

Structure Lattice :={
  lt_carrier :> Type;
  lt_and : lt_carrier -> lt_carrier -> lt_carrier;
  lt_or : lt_carrier -> lt_carrier -> lt_carrier;
  lt_zero : lt_carrier;
  lt_one : lt_carrier;
  lt_and_commute : forall x y, lt_and x y = lt_and y x;
  lt_or_commute : forall x y, lt_or x y = lt_or y x;
  lt_and_associcate : forall x y z, lt_and x (lt_and y z) = lt_and (lt_and x y) z;
  lt_or_associate : forall x y z, lt_or x (lt_or y z) = lt_or (lt_or x y) z;
  lt_or_absorb : forall x y, lt_or x (lt_and x y)=x;
  lt_and_absorb : forall x y, lt_and x (lt_or x y)=x;
  lt_zero_identity_r : forall x, lt_or x lt_zero = x;
  lt_one_identity_r : forall x, lt_and x lt_one = x;
  lt_distribute_or : forall x y z, lt_or x (lt_and y z) = lt_and (lt_or x y) (lt_or x z);
  lt_distribute_and : forall x y z, lt_and x (lt_or y z) = lt_or (lt_and x y) (lt_and x z)
}.

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

Structure ProximityLattice :=
  {
    plt_lattice :> Lattice;
    plt_approx : plt_lattice -> plt_lattice -> Prop;
    plt_trans : forall x y z, plt_approx x y -> plt_approx y z -> plt_approx x z;
    plt_approx_or : forall x y z , plt_approx x z /\ plt_approx y z <-> plt_approx (x || y) z;
    plt_approx_or_interpolate :
      forall x y z , plt_approx x (y || z) -> (exists y' z', plt_approx y' y /\ plt_approx z' z /\ plt_approx x (y' || z'));
    plt_approx_and : forall x y z , plt_approx x y /\ plt_approx x z <-> plt_approx x (y && z);
    plt_approx_one : forall x , x <> 1 -> plt_approx x 1;
    plt_interpolate : forall x y, plt_approx x y -> (exists z, plt_approx x z /\ plt_approx z y)
  }.

Notation "x << y" := (plt_approx _ x y)(at level 70, no associativity).

Lemma or_approx_monotone_r (A : ProximityLattice) (x y1 y2 : A) :
  y1 << y2 -> x || y1 << x || y2.
Proof.
  admit.
Admitted.

Section FiniteJoins.
  (* Definition and basic facts about finite joins. *)

  Fixpoint list_join {A : Lattice} (xs : list A) : A :=
    match xs with
    | nil => 1
    | cons y ys => y || list_join ys
    end.

End FiniteJoins.

Structure ApproximableMapping (A B : ProximityLattice) :=
  {
    plt_hom :> A -> B -> Prop;
    plt_hom_interpolate_l : forall x y , plt_hom x y -> (exists z, x << z /\ plt_hom z y);
    plt_hom_interpolate_r : forall x y , plt_hom x y -> (exists z, z << y /\ plt_hom x z);
    plt_hom_or : forall x y z , plt_hom x z /\ plt_hom y z <-> plt_hom (x || y) z;
    plt_hom_one : forall x, x << 1 -> plt_hom x 1;
    plt_hom_and : forall x y z , plt_hom x y /\ plt_hom x z <-> plt_hom x (y && z);
    plt_hom_refine :
      forall x ys, plt_hom x (list_join ys) ->
                   exists zs, x << list_join zs /\ forall z, In z zs -> exists y, In y ys /\  plt_hom z y
  }.

Definition plt_id {A : ProximityLattice} : ApproximableMapping A A.
Proof.
  refine {| plt_hom := fun x y => x << y |}.
  - now apply plt_interpolate.
  - intros.
    destruct (plt_interpolate A x y H) as [w [? ?]].
    now exists w.
  - now apply plt_approx_or.
  - auto.
  - now apply plt_approx_and.
  - intros x ys. generalize x; clear x.
    induction ys.
    + (* ys is empty list *)
      intros. exists nil. split.
      * assumption.
      * intros z G. elim G.
    + { (* induction step *)
        intros x H.
        simpl in H.
        destruct (plt_approx_or_interpolate A x a (list_join ys) H) as [u [v [? [H1 ?]]]].
        destruct (IHys v H1) as [us [? ?]].
        exists (cons u us).
        split.
        - simpl.
          apply (plt_trans _ x (u || v)).
          + assumption.
          + now apply or_approx_monotone_r.
        - intros z ?.
          destruct H5.
          + exists a. split.
            * simpl. now left.
            * now destruct H5.
          + destruct (H4 z H5) as [y' [? ?]].
            exists y'. split.
            * simpl. now right.
            * assumption.
      }
Admitted.


