Require Import List.

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

Structure ProximityLattice :=
  {
    plt_lattice :> Lattice;
    plt_approx : plt_lattice -> plt_lattice -> Prop;
    plt_trans : forall x y z, plt_approx x y -> plt_approx y z -> plt_approx x z;
    plt_approx_or : forall x y z , plt_approx x z /\ plt_approx y z <-> plt_approx (x || y) z;
    plt_approx_or_interpolate :
      forall x y z , plt_approx x (y || z) -> (exists y' z', plt_approx y' y /\ plt_approx z' z /\ plt_approx x (y' || z'));
    plt_approx_and : forall x y z , plt_approx x y /\ plt_approx x z <-> plt_approx x (y && z);
    plt_approx_one : forall x , plt_approx x 1;
    plt_interpolate : forall x y, plt_approx x y -> (exists z, plt_approx x z /\ plt_approx z y)
  }.

Notation "x << y" := (plt_approx _ x y)(at level 70, no associativity).

Lemma plt_approx_or_l (A : ProximityLattice) (x y z : A) :
  (x || y) << z -> x << z.
Proof.
  apply plt_approx_or.
Defined.


Lemma plt_approx_or_r (A : ProximityLattice) (x y z : A) :
  (x || y) << z -> y << z.
Proof.
  apply plt_approx_or.
Defined.

Lemma plt_approx_and_l (A : ProximityLattice) (x y z : A) :
  z << x && y -> z << x.
Proof.
  apply plt_approx_and.
Defined.



Lemma plt_approx_and_r (A : ProximityLattice) (x y z : A) :
  z << x && y -> z << y.
Proof.
  apply plt_approx_and.
Defined.


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
          + admit.
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


(*
Inductive Colors := White | Black.
Definition color_and (b1 : Colors) (b2 : Colors) : Colors := 
  match b1  with 
  | White , White => White 
  | Black , White => Black
  end.

Definition color_or (b1 : Colors) (b2 : Colors) : Colors := 
  match b1 with 
  | White => b2 
  | Black => Black
  end.

Definition Two_Lattice : Lattice.
Proof.
   refine{| lt_carrier := Colors;
            lt_and := fun x y => color_and x y;
            lt_or := fun x y => color_or x y;
            lt_zero := White;
            lt_one := Black
|}.
intros.
apply lt_and_commute.
*)

Definition TwoLattice : Lattice.
Proof.
  (* We use bool and its operations from the standard library *)
  refine {| lt_carrier := bool ;
            lt_and := andb;
            lt_or := orb;
            lt_zero := false;
            lt_one := true|}; repeat (intros [|]); reflexivity.
Defined.


(*Definition Two_hom(b1 b2 : Two_Lattice): Prop :=
  match b1, b2 with
    | true , true => True
    | true , false => False
    | false , true => True
    | false , false => True
  end.


Lemma Ttt: Two_hom true true =True.
Proof.
reflexivity.
Qed.
*)

(*Definition Two_approx (a : TwoLattice) (b : TwoLattice) :=
=======
Definition Two_approx (a : TwoLattice) (b : TwoLattice) :=
>>>>>>> origin/master
  match a with
    | false => True
    | true => False
  end.
<<<<<<< HEAD
*)

Definition Two_approx(b1 b2 : TwoLattice): Prop :=
  match b1, b2 with
    | true , true => True
    | true , false => False
    | false , true => True
    | false , false => True
  end.


Definition Two_Proximity : ProximityLattice.
Proof.
   refine {| plt_lattice := TwoLattice ;
             plt_approx := Two_approx
          |}.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ;
       tauto || (intros _ ; 
                 ((exists false ; 
                          ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto))
                  ) ||
                  (exists true ;
                          ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto))
                ))).
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ;
       (tauto || (intros _ ; ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto)))).
Defined.

Lemma pair_equal (A B : Type) (x1 x2 : A) (y1 y2 : B) :
  x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof.
  intros [] [] ; reflexivity.
Defined.

Definition LatticeProduct (A B : Lattice) : Lattice.
Proof.
  refine {| lt_carrier := A * B ;
            lt_or := (fun x y => (fst x || fst y, snd x || snd y)) ;
            lt_and := (fun x y => (fst x && fst y, snd x && snd y)) ;
            lt_zero := (0, 0) ;
            lt_one := (1, 1)
         |} ;
  repeat intros [? ?] ; simpl ; apply pair_equal ;
    auto with lt_hints.
Defined.

Definition ProximityProduct (A B : ProximityLattice) : ProximityLattice.
Proof.
  refine {|  plt_lattice := LatticeProduct A B ;
             plt_approx := (fun x y => (fst x << fst y) /\ (snd x << snd y))
         |}.
  - intros [x1 y1] [x2 y2] [x3 y3] [H1 H2] [H3 H4]; simpl in * ; split.
    + eapply plt_trans ; eassumption.
    + eapply plt_trans ; eassumption.
  - repeat intros [? ?] ; simpl in * ; split.
    + intros [[? ?] [? ?]]. split.
      * apply plt_approx_or ; tauto.
      * apply plt_approx_or ; tauto.
    + intros [? ?]. repeat split.
      * eapply plt_approx_or_r.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_r.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_l.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_l.
        rewrite lt_or_commute.
        eassumption.
  - intros [x1 y1] [x2 y2] [x3 y3] [H1 H2] ; simpl in *.
    destruct (plt_approx_or_interpolate _ x1 x2 x3 H1) as [x2' [x3' [? [? ?]]]].
    destruct (plt_approx_or_interpolate _ _ _ _ H2) as [y2' [y3' [? [? ?]]]].
    exists (x2', y2').
    exists (x3', y3').
    tauto.
  - intros [x1 y1] [x2 y2] [x3 y3] ; simpl in *.
    split.
    + intros [[? ?] [? ?]] ; split.
      * now apply plt_approx_and.
      * now apply plt_approx_and.
    + intros [? ?] ; repeat split ; eauto using plt_approx_and_l, plt_approx_and_r.
  (* intros [x1 y1] H ; simpl in * ; split.
    * admit. (* XXX we have a real mathematical problem here (not just Coq). *)
    * admit.
  - admit.*)
Admitted.


(*
Definition Two_Proximity : ProximityLattice.
Proof.
   refine {| plt_lattice := TwoLattice ;
             plt_approx := Two_approx
          |}.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ;
       tauto || (intros _ ; 
                 ((exists false ; 
                          ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto))
                  ) ||
                  (exists true ;
                          ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto))
                ))).
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ; tauto.
   - repeat intros [|] ; simpl ;
       (tauto || (intros _ ; ((exists false ; simpl ; tauto) || (exists true ; simpl ; tauto)))).
Defined.

Lemma pair_equal (A B : Type) (x1 x2 : A) (y1 y2 : B) :
  x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof.
  intros [] [] ; reflexivity.
Defined.

Definition LatticeProduct (A B : Lattice) : Lattice.
Proof.
  refine {| lt_carrier := A * B ;
            lt_or := (fun x y => (fst x || fst y, snd x || snd y)) ;
            lt_and := (fun x y => (fst x && fst y, snd x && snd y)) ;
            lt_zero := (0, 0) ;
            lt_one := (1, 1)
         |} ;
  repeat intros [? ?] ; simpl ; apply pair_equal ;
    auto with lt_hints.
Defined.

Definition ProximityProduct (A B : ProximityLattice) : ProximityLattice.
Proof.
  refine {|  plt_lattice := LatticeProduct A B ;
             plt_approx := (fun x y => (fst x << fst y) /\ (snd x << snd y))
         |}.
  - intros [x1 y1] [x2 y2] [x3 y3] [H1 H2] [H3 H4]; simpl in * ; split.
    + eapply plt_trans ; eassumption.
    + eapply plt_trans ; eassumption.
  - repeat intros [? ?] ; simpl in * ; split.
    + intros [[? ?] [? ?]]. split.
      * apply plt_approx_or ; tauto.
      * apply plt_approx_or ; tauto.
    + intros [? ?]. repeat split.
      * eapply plt_approx_or_r.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_r.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_l.
        rewrite lt_or_commute.
        eassumption.
      * eapply plt_approx_or_l.
        rewrite lt_or_commute.
        eassumption.
  - intros [x1 y1] [x2 y2] [x3 y3] [H1 H2] ; simpl in *.
    destruct (plt_approx_or_interpolate _ x1 x2 x3 H1) as [x2' [x3' [? [? ?]]]].
    destruct (plt_approx_or_interpolate _ _ _ _ H2) as [y2' [y3' [? [? ?]]]].
    exists (x2', y2').
    exists (x3', y3').
    tauto.
  - intros [x1 y1] [x2 y2] [x3 y3] ; simpl in *.
    split.
    + intros [[? ?] [? ?]] ; split.
      * now apply plt_approx_and.
      * now apply plt_approx_and.
    + intros [? ?] ; repeat split ; eauto using plt_approx_and_l, plt_approx_and_r.
    - admit. (* intros [x1 y1] H ; simpl in * ; split.*)
    - admit. (* XXX we have a real mathematical problem here (not just Coq). *)
  
Admitted.
*)
