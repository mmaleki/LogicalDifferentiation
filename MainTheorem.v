(*Require Import QArith.
Require Import QArith.Qreals.*)
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Lra.

Local Open Scope R_scope.

Axiom cheating : forall (A : Type), A.
Ltac cheat := apply cheating.

(* tactics for dealing with Rmin and Rmax *)
Ltac unfold_Rle_dec :=
  match goal with
  | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) ; simpl ; unfold_Rle_dec
  | _ : context [Rle_dec ?a ?b] |- _ =>
    destruct (Rle_dec a b) ; simpl ; unfold_Rle_dec
  | _ => idtac
  end.

Ltac handle_Rminmax :=
  simpl ; unfold Rmin, Rmax in * ; unfold_Rle_dec.

(* Basic definitions. *)

Structure OpenInterval := {
  op_lower : R ;
  op_upper : R ;
  op_proper : op_lower < op_upper
}.

Structure ClosedInterval := {
  cl_lower : R ;
  cl_upper : R ;
  cl_proper : cl_lower <= cl_upper
}.

Structure PositiveInterval := {
  pos_interval :> OpenInterval ;
  pos_positive : op_lower pos_interval > 0
}.


Definition separated (a b : OpenInterval) :=
 op_upper a < op_lower b \/ op_upper b < op_lower a.

Definition overlap (a b : OpenInterval) :=
  (op_lower a < op_lower b /\ op_lower b < op_upper a) \/
  (op_lower b < op_lower a /\ op_lower a < op_upper b).


(* Note: this join only really works when applied to overlapping intervals. *)
Definition join (a b : OpenInterval) : OpenInterval.
Proof.
  refine {| op_lower := Rmin (op_lower a) (op_lower b) ;
            op_upper := Rmax (op_upper a) (op_upper b) |}.
  destruct a as [a1 a2 Pa].
  destruct b as [b1 b2 Pb].
  unfold Rmin, Rmax; simpl.
  handle_Rminmax ; lra.
Defined.

Definition closure : OpenInterval -> ClosedInterval.
Proof.
  intro a.
  refine {| cl_lower := op_lower a ; cl_upper := op_upper a |}.
  apply Rlt_le, op_proper.
Defined.

Definition opop_inside (a : OpenInterval) (b : OpenInterval) :=
  op_lower b <= op_lower a /\ op_upper a <= op_upper b.

Definition clop_inside (a : ClosedInterval) (b : OpenInterval) :=
  op_lower b < cl_lower a /\ cl_upper a < op_upper b.

Definition opcl_inside (a : OpenInterval) (b : ClosedInterval) :=
  cl_lower b <= op_lower a /\ op_upper a <= cl_upper b.

Definition clcl_inside a b :=
  cl_lower b <= cl_lower a /\ cl_upper a <= cl_upper b.

Definition well_inside (a b : OpenInterval) :=
  op_lower b < op_lower a /\ op_upper a < op_upper b.

Definition well_inside_tran a b c :
  well_inside a b -> well_inside b c -> well_inside a c.
Proof.
  destruct a, b, c.
  unfold well_inside.
  simpl.
  lra.
Qed.

(* Multiplication of a closed interval by a scalar. *)
Definition cl_scalar_mul (x : R) (a : ClosedInterval) : ClosedInterval.
Proof.
  refine {| cl_lower := Rmin (x * cl_lower a) (x * cl_upper a) ;
            cl_upper := Rmax (x * cl_lower a) (x * cl_upper a) |}.
  now apply Rminmax.
Defined.

(* Multiplication of an open interval by a non-zero scalar. *)
Definition op_scalar_mul (x : R) (H : x <> 0) (a : OpenInterval) :
  OpenInterval.
Proof.
  refine {| op_lower := Rmin (x * op_lower a) (x * op_upper a) ;
            op_upper := Rmax (x * op_lower a) (x * op_upper a) |}.
  destruct a.
  handle_Rminmax ; nra.
Defined.

Definition cl_in (x : R) (a : ClosedInterval) :=
  cl_lower a <= x /\ x <= cl_upper a.

Definition op_in (x : R) (a : OpenInterval) :=
  op_lower a < x /\ x < op_upper a.

(* If we make separated intervals smaller they are still separated. *)
Lemma separated_smaller a b a' b' :
   well_inside a' a -> well_inside b' b -> separated a b -> separated a' b'.
Proof.
  destruct a as [a1 a2 Pa].
  destruct b as [b1 b2 Pb].
  destruct a' as [a1' a2' Pa'].
  destruct b' as [b1' b2' Pb'].
  unfold well_inside, separated; simpl.
  lra.
Qed.

(* f is continuous on a closed interval a *)
Definition cl_continuous_on (f : R -> R) (a : ClosedInterval) :=
  forall x, cl_in x a -> continuity_pt f x.

Lemma cl_in_monotone x a b :
  cl_in x a -> clcl_inside a b -> cl_in x b.
Proof.
  destruct a, b.
  unfold cl_in, clcl_inside.
  simpl in *.
  lra.
Qed.

Lemma cl_continuous_restrict (f : R -> R) a b :
  cl_continuous_on f b -> clcl_inside a b -> cl_continuous_on f a.
Proof.
  intros H in_a_b x x_in_a.
  now apply H, (cl_in_monotone x a).
Qed.

Definition cl_lower_bound (f : R -> R) (a : ClosedInterval) (m : R) :=
  forall x, cl_in x a -> m <= f x.

Definition cl_upper_bound (f : R -> R) (a : ClosedInterval) (m : R) :=
  forall x, cl_in x a -> f x <= m.

(* the minimum of a continuous f on a closed interval a *)
Axiom cl_min :
  forall (f : R -> R) (a : ClosedInterval),
  cl_continuous_on f a ->
  { m : R | cl_lower_bound f a m /\
            (forall m', cl_lower_bound f a m' -> m' <= m) }.

Axiom cl_max :
  forall (f : R -> R) (a : ClosedInterval),
  cl_continuous_on f a ->
  { m : R | cl_upper_bound f a m /\
            (forall m', cl_upper_bound f a m' -> m <= m') }.

(* b is the image of a by f *)
Definition cl_is_image (f : R -> R) (a b : ClosedInterval) :=
  (forall x, cl_in x a -> cl_in (f x) b) /\
  (forall y, cl_in y b -> exists x, cl_in x a /\ f x = y).

(* The image of a closed interval by a contunuous function is a closed interval. *)
Definition cl_image (f : R -> R) (a : ClosedInterval) :
  cl_continuous_on f a ->
  { b : ClosedInterval | cl_is_image f a b }.
Proof.
  intro cont_f.
  destruct (cl_min f a cont_f) as [m m_is_glb].
  destruct (cl_max f a cont_f) as [M M_is_lub].
  assert (m_le_M : m <= M).
  { cheat. }
  exists {| cl_lower := m ; cl_upper := M ; cl_proper := m_le_M |}.
  split.
  - intros x x_in_a.
    split.
    + now apply m_is_glb.
    + now apply M_is_lub.
  - unfold cl_in; simpl.
    intros y [m_y y_M].
    cheat. (* intermediate value theorem *)
Defined.

(* Substraction of open intervals. *)
  Definition op_subtract (a b : OpenInterval) : OpenInterval.
Proof.
  refine {| op_lower := op_lower a - op_upper b ;
            op_upper := op_upper a - op_lower b |}.
  destruct a, b.
  simpl in *.
  lra.
Defined.

 Definition cl_subtract (a b : ClosedInterval) : ClosedInterval.
Proof.
  refine {| cl_lower := cl_lower a - cl_upper b ;
            cl_upper := cl_upper a - cl_lower b |}.
  destruct a, b.
  simpl in *.
  lra.
Defined.

Lemma minus_interval_image (f : R -> R)
      (a1 a2 : ClosedInterval)
      (c : OpenInterval) :
  forall (cont_f_a1 : cl_continuous_on f a1)
         (cont_f_a2 : cl_continuous_on f a2),
    (forall x y, cl_in x a1 ->
                 cl_in y a2 ->
                 op_in (f x - f y) c)
    ->
    clop_inside
      (cl_subtract
         (proj1_sig (cl_image f a1 cont_f_a1))
         (proj1_sig (cl_image f a2 cont_f_a2)))
      c.
Proof.
  intros cont_f_a1 cont_f_a2 H.
  destruct (cl_image f a1 cont_f_a1) as [fa1 [Ha1 Ga1]].
  destruct (cl_image f a2 cont_f_a2) as [fa2 [Ha2 Ga2]].
  simpl.
  unfold cl_is_image in *.
  destruct fa1 as [fa1_m fa1_M fa1_prop].
  destruct fa2 as [fa2_m fa2_M fa2_prop].
  destruct a1 as [a11 a12 a1_prop].
  destruct a2 as [a21 a22 a2_prop].
  unfold cl_in, cl_subtract, clop_inside in *.
  simpl in *.
  split.
  - destruct (Ga1 fa1_m) as [x_m [xm_in_a1 fxm_fa1m]].
    { lra. }
    destruct (Ga2 fa2_M) as [x_M [xM_in_a2 fxM_fa2M]].
    { lra. }
    rewrite <- fxm_fa1m.
    rewrite <- fxM_fa2M.
    now apply (H x_m x_M).
  - destruct (Ga1 fa1_M) as [y_M [yM_in_a1 fyM_fa1M]].
    { lra. }
    destruct (Ga2 fa2_m) as [y_m [ym_in_a2 fym_fa2m]].
    { lra. }
    rewrite <- fyM_fa1M.
    rewrite <- fym_fa2m.
    now apply (H y_M y_m).
Qed.


Definition op_multiply (a b : OpenInterval) : OpenInterval.
Proof.
  destruct a as [a1 a2 ?].
  destruct b as [b1 b2 ?].
  refine {| op_lower := Rmin (Rmin (a1 * b1) (a1 * b2)) (Rmin (a2 * b1) (a2 * b2)) ;
            op_upper := Rmax (Rmax (a1 * b1) (a1 * b2)) (Rmax (a2 * b1) (a2 * b2)) |}.
  handle_Rminmax ; nra.
Defined.

Definition Approx (f : R -> R) (a O : OpenInterval) :=
  forall x, cl_in x (closure a) -> op_in (f x) O.

Definition delta (a : OpenInterval) (b : ClosedInterval) (f : R -> R) :=
   forall x y : R, op_in x a -> op_in y a ->
                cl_in (f x - f y) (cl_scalar_mul (x - y) b).

Definition Delta (a O : OpenInterval) (A : OpenInterval -> OpenInterval -> Prop) :=
  forall a1 a2,
    well_inside a1 a ->
    well_inside a2 a ->
    separated a1 a2 ->
    exists a1' a2',
      A a1 a1' /\ A a2 a2' /\
      well_inside (op_subtract a1' a2') (op_multiply O (op_subtract a1 a2)).

Definition strong_delta (a : OpenInterval) (b : ClosedInterval) (f : R -> R) :=
   exists (a' b' : OpenInterval),
     well_inside a a' ->
     opcl_inside b' b ->
     forall x y : R, op_in x a' -> op_in y a' ->
                     cl_in (f x - f y) (cl_scalar_mul (x - y) (closure b')).

Definition StrongDelta (a O : OpenInterval) (A : OpenInterval -> OpenInterval -> Prop) :=
   exists a' O',
     well_inside a a' ->
     well_inside O' O ->
     forall a1 a2,
       well_inside a1 a' ->
       well_inside a2 a' ->
       separated a1 a2 ->
       exists a1' a2',
         A a1 a1' /\ A a2 a2' /\
         well_inside (op_subtract a1' a2') (op_multiply O' (op_subtract a1 a2)).

Structure bowtie (a : OpenInterval) (b : ClosedInterval) := {
  bow_map :> R -> R ;
  bow_lipschitz :
    forall x y : R, op_in x a -> op_in y a ->
                cl_in (bow_map x - bow_map y) (cl_scalar_mul (x - y) b)
}.

Structure ApproximableMap : Type := {
  app_map :> OpenInterval -> OpenInterval -> Prop ; (* this is our A *)
  app_monotone_r : forall a b c, app_map a b -> well_inside b c -> app_map a c ;
  app_monotone_l : forall a b c, app_map b c -> well_inside a b -> app_map a c ;
  app_total : forall a, exists b, app_map a b ; (* imagine: a A 1 *)
  app_disjoint : forall a b c, separated b c -> ~ (app_map a b /\ app_map a c) ; (* imagine: ~ (a A 0) *)
  app_directed : forall a b c, app_map a b -> app_map a c ->
                               exists d, well_inside d b /\ well_inside d c /\ app_map a d ;
  app_converge :
    forall a b c, overlap b c ->
    app_map a (join b c) ->
    exists a1 a2, overlap a1 a2 /\ well_inside a (join a1 a2) /\
                  app_map a1 b /\ app_map a2 c
  (* exercise: define this so that you can prove approximable_filter_maps below. *)
}.

Structure Bowtie (a O : OpenInterval)  := {
  Bow_map :> ApproximableMap ;
  Bow_lipschitz : Delta a O Bow_map
}.

(* A completely prime filter w.r.t. to the well-inside order. *)
Structure CompleteFilter : Type := {
  cf_filter :> OpenInterval -> Prop ;
  cf_monotone : forall a b, well_inside a b -> cf_filter a -> cf_filter b ;
  cf_inhabited : exists a, cf_filter a ; (* imagine: (-inf, inf) is in cf_filter *)
  cf_disjoint : forall a b, separated a b -> ~ (cf_filter a /\ cf_filter b) ; (* imagine: empty set is not in cf_filter *)
  cf_directed : forall a b, cf_filter a -> cf_filter b -> exists c,
                                well_inside c a /\ well_inside c b /\ cf_filter c ;
  cf_converge: forall a b, overlap a b -> cf_filter (join a b) -> cf_filter a \/ cf_filter b (* the filter is prime *)
}.


Definition frame_map
           (A : OpenInterval -> OpenInterval -> Prop)
           (F : OpenInterval -> Prop) : OpenInterval -> Prop :=
  fun b => exists a, A a b /\ F a.

Definition filter_map (A : ApproximableMap) : CompleteFilter -> CompleteFilter.
Proof.
  intro F. 
  refine {| cf_filter := frame_map A F |}.
  - intros a b Wab [c [Aca Fc]].
    exists c.
    split.
    + now apply (app_monotone_r _ c a b).
    + assumption.
  - unfold  frame_map. 
    destruct (cf_inhabited F) as [a' Fa'].
    destruct (app_total A a') as [a'' Aa'a''].
    now exists a'', a'.
  - intros a b sep_ab.
    intros [[c [Aca Fc]] [d [Adb Fd]]]. 
    destruct (cf_directed F c d Fc Fd) as [e [Wea [Wed Fe]]].
    assert (Aea : A e a).
    { eapply app_monotone_l.
      - exact Aca.
      - assumption. }
    assert (Aeb : A e b).
    { eapply app_monotone_l.
      - exact Adb.
      - assumption. }
    pose (G := app_disjoint A e a b sep_ab).
    now absurd (A e a /\ A e b).
   - intros a b [c [Aca Fc]] [d [Adb Fd]].
    destruct (cf_directed F c d Fc Fd) as [e [Wec [Wed Fe]]].
    assert (Aea : A e a).
    { eapply app_monotone_l.
      - exact Aca.
      - assumption. }
    assert (Aeb : A e b).
    { eapply app_monotone_l.
      - exact Adb.
      - assumption. }
    destruct (app_directed A e a b Aea Aeb) as [c' [Wc'a [Wc'b Aec']]].
    exists c'.
    split ; [ assumption  | split ; [ assumption | unfold frame_map] ].
    now exists e.
  - intros a b ovl_ab [c [Acjab Fc]].
    unfold frame_map.
    destruct (app_converge A c a b ovl_ab Acjab) as [a' [b' [ovl_a'b' [Wcja'b' [Aa'a Ab'b]]]]].
    assert (Fja'b' : F (join a' b')).
    { eapply cf_monotone. exact Wcja'b'. assumption. }
    destruct (cf_converge F a' b' ovl_a'b' Fja'b') as [Fa' | Fb'].
    + left. now exists a'.
    + right. now exists b'.
Defined.

Definition point2filter (x : R) : CompleteFilter.
Proof.
  intros.
  refine {| cf_filter := fun a => op_in x a |}.
  - intros a b Wab x_in_a.
    unfold op_in in *.
    destruct Wab.
    destruct x_in_a.
    split.
     + lra.
     + lra.
   - assert (C : x-1 < x+1) by lra.
     exists {| op_lower := x-1; op_upper := x+1; op_proper := C |}. 
     unfold op_in in *.
     simpl in *.
     lra.
   - intros.
     unfold not.
     intros.
     destruct H. 
     unfold op_in in *. 
     destruct H0, H1.
     + destruct H0.
       lra.
     + destruct H0. 
       unfold op_in in *.
       lra.
   - intros.
     destruct a as [a1 a2 a_prop].
     destruct b as [b1 b2 b_prop].
     destruct H. simpl in *.
     destruct H0. simpl in *.
     unfold well_inside in *. simpl in *.
     assert (G: (Rmax a1 b1 +x)/2 < (Rmin a2 b2 +x)/2).
     { handle_Rminmax ; lra. }
     exists {| op_lower := (Rmax a1 b1 + x) / 2;
               op_upper := (Rmin a2 b2 + x) / 2;
               op_proper := G |}.
     simpl in *.
     repeat split ; handle_Rminmax ; lra.
   - intros a b H [G1 G2].
     destruct a, b.
     unfold overlap, join, op_in in * ; simpl in *.
     handle_Rminmax ; lra.
Defined.

Lemma lower_below_upper (F : CompleteFilter) a b :
  F a -> F b -> op_lower a < op_upper b.
Proof.
   intros Fa Fb.
   destruct (cf_directed F a b Fa Fb) as [c[Wca [Wcb Fc]]].
   destruct Wca, Wcb.
   eapply Rlt_trans.
   + apply H.
   + apply (Rlt_trans (op_lower c) (op_upper c) (op_upper b)).
     - apply (op_proper c).
     - assumption.
Defined.

Lemma filter2point (F : CompleteFilter) : R.
Proof.
  (* The set of lower bounds of the number we are constructing. *)
  pose (E := fun y => exists a, F a /\ y < op_lower a ).
  assert (bE : bound E).
  { destruct (cf_inhabited F) as [a Fa].
    exists (op_upper a).
    intros y [b [Fb x_leq_b]].
    apply Rlt_le.
    apply (Rle_lt_trans y (op_lower b) (op_upper a)).
    + now apply Rlt_le.
    + now apply (lower_below_upper F).
  }
  assert (inhE : exists y : R, E y).
  { destruct (cf_inhabited F) as [a Fa].
    exists (op_lower a - 1).
    unfold E.
    exists a.
    split.
    - assumption.
    - lra.
  }
  destruct (completeness E bE inhE) as [x lub_x].
  exact x.
Defined.

Lemma filter_point_inverse (x : R) :
  x = filter2point (point2filter x ).
Proof.
 pose (E := fun y => exists a, (point2filter x) a /\ y < op_lower a ).
   assert (bE : bound E).
  { destruct (cf_inhabited (point2filter x)) as [a Fa].
    exists (op_upper a).
    intros y [b [Fb x_leq_b]].
    apply Rlt_le.
    apply (Rle_lt_trans y (op_lower b) (op_upper a)).
    + now apply Rlt_le.
    + now apply (lower_below_upper (point2filter x)).
  }
 assert (inhE : exists y : R, E y).
  { destruct (cf_inhabited (point2filter x)) as [a Fa].
    exists (op_lower a - 1).
    unfold E.
    exists a.
    split.
    - assumption.
    - lra.
  }
  destruct (completeness E bE inhE) as [z lub_z].
  assert (Eq: z = filter2point (point2filter x)).
  admit.
Admitted.
 
 

Lemma point_filter_inverse (F : CompleteFilter) :
  forall a, F a <-> (point2filter (filter2point F)) a.
Admitted. (* exercise *)

Definition dual_fun (A : ApproximableMap) (x : R) :=
  filter2point (filter_map A (point2filter x)).

Definition interpol (a : ClosedInterval) (b : OpenInterval) :
  clop_inside a b -> exists b' : OpenInterval, clop_inside a b' /\ well_inside b' b.
Proof.
   intros.
   destruct a, b.
   rename
      cl_lower0 into a1,
      cl_upper0 into a2,
      cl_proper0 into a_prop,
      op_lower0 into b1,
      op_upper0 into b2,
      op_proper0 into b_prop.
    pose (c1 := (a1+b1)*(1/2)).
    pose (c2 := (a2+b2)*(1/2)).
    assert (C : c1 < c2).
    { unfold c1, c2. lra . }
    exists {| op_lower := c1; op_upper := c2; op_proper := C |}.
    unfold clop_inside in *.
    unfold op_lower in *.
    unfold cl_lower in *.
    unfold cl_upper in *.
    unfold op_upper in *.
    unfold well_inside in *.
    unfold c1, c2 in *.
    simpl.
    nra.
Defined.

Lemma R_Hausdorff (x y : R) :
  x <> y ->
  exists a b : OpenInterval, op_in x a /\ op_in y b /\ (separated a b).
Proof.
  intro Nxy.
  destruct (Rdichotomy x y Nxy).
  - pose (a1 := x - 1).
    pose (a2 := (2 * x + y) / 3).
    assert (a_prop : a1 < a2).
    { unfold a1, a2. lra. }
    pose (b1 := (x + 2 * y) / 3).
    pose (b2 := y + 1).
    assert (b_prop : b1 < b2).
    { unfold b1, b2. lra. }
    exists {| op_lower := a1; op_upper := a2; op_proper := a_prop |}.
    exists {| op_lower := b1; op_upper := b2; op_proper := b_prop |}.
    unfold op_in, separated; simpl.
    unfold a1, a2, b1, b2.
    lra.
  - pose (a2 := x + 1).
    pose (a1 := (2 * x + y) / 3).
    assert (a_prop : a1 < a2).
    { unfold a1, a2. lra. }
    pose (b2 := (x + 2 * y) / 3).
    pose (b1 := y - 1).
    assert (b_prop : b1 < b2).
    { unfold b1, b2. lra. }
    exists {| op_lower := a1; op_upper := a2; op_proper := a_prop |}.
    exists {| op_lower := b1; op_upper := b2; op_proper := b_prop |}.
    unfold op_in, separated; simpl.
    unfold a1, a2, b1, b2.
    lra.
Qed.

Lemma point_directedness (x : R) (a b : OpenInterval) :
  op_in x a -> op_in x b ->
  exists c, op_in x c /\ well_inside c a /\ well_inside c b.
Proof.
   intros x_in_a x_in_b.
   destruct x_in_a, x_in_b.
   pose (z1 := Rmax (op_lower a) (op_lower b)).
   pose (z2 := Rmin (op_upper a) (op_upper b)).
   unfold Rmax in *. 
   destruct (Rle_dec (op_lower a) (op_lower b)). 
   unfold Rmin in *.
   destruct (Rle_dec (op_upper a) (op_upper b)).
   assert (G: (z1+x)/2 < (z2+x)/2).
      {unfold z1, z2. lra. } 
   exists {|op_lower := (z1+x)/2; 
               op_upper := (z2+x)/2;
               op_proper := G |}.
    - unfold op_in in *. simpl in *.
      split. 
      + split.
        ** unfold z1. lra.
        **  unfold z2. lra.
      + split.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
   - assert (G: (z1+x)/2 < (z2+x)/2).
      {unfold z1, z2. lra. } 
      exists {|op_lower := (z1+x)/2; 
               op_upper := (z2+x)/2;
               op_proper := G |}.
      unfold op_in in *. simpl in *.
      split. 
      + split.
        ** unfold z1. lra.
        **  unfold z2. lra.
      + split.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
    - unfold Rmin in *.
      destruct (Rle_dec (op_upper a) (op_upper b)).
      assert (G: (z1+x)/2 < (z2+x)/2).
      {unfold z1, z2. lra. } 
      exists {|op_lower := (z1+x)/2; 
               op_upper := (z2+x)/2;
               op_proper := G |}.
      unfold op_in in *. simpl in *.
      split. 
      + split.
        ** unfold z1. lra.
        **  unfold z2. lra.
      + split.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
        ** unfold well_inside in *. simpl in *. split.
           -- unfold z1. lra.
           -- unfold z2. lra.
      +  assert (G: (z1+x)/2 < (z2+x)/2).
      {unfold z1, z2. lra. } 
      exists {|op_lower := (z1+x)/2; 
               op_upper := (z2+x)/2;
               op_proper := G |}.
      unfold op_in in *. simpl in *.
      unfold well_inside in *. simpl in *.
      split. 
         ***  unfold z1, z2.
              lra.
         *** unfold z1, z2. lra.
Defined.


Lemma closed_in_from_open_in (x : R) (a : ClosedInterval) :
  ((forall c, clop_inside a c -> op_in x c) <-> cl_in x a).
Proof.
  split. 
  - intro H.
    unfold cl_in.
    split.
    + destruct a as [a1 a2 prop_a].
      unfold clop_inside in *.
      simpl in *.
      admit.
    + admit.
  - intros x_in_a c ins_ac.
    unfold well_inside, op_in, clop_inside, cl_in in *.
    destruct a, c.
    simpl in *.
    lra.
Admitted.
Print clop_inside.
Check op_subtract.

Lemma scott_continuity (b1 b2 : ClosedInterval) (O: OpenInterval):
  clop_inside (cl_subtract b1 b2) O ->
  exists c1 c2 : OpenInterval,
    clop_inside b1 c1 /\ clop_inside b2 c2 /\ well_inside (op_subtract c1 c2) O.
Proof.
   intros.
   destruct b1 as [x1 y1 b1_prop].
   destruct b2 as [x2 y2 b2_prop].
   destruct O as [O1 O2 O_prop].
   destruct H as [H1 H2].
   unfold clop_inside, well_inside in *.
   simpl in *.
   pose (d1 := (O2 - y1 + x2)/4).
   pose (d2 := (x1 - y2 - O1)/4).
   pose (d := Rmin d1 d2).
   unfold Rmin in *.
   destruct (Rle_dec d1 d2). 
   - assert (G1 : x1 - d < y1 +d).
     {unfold d. unfold d1. lra. }
     assert (G2 : x2 - d < y2 +d).
     {unfold d. unfold d1. lra. }
     exists {| op_lower := x1 - d ;
               op_upper := y1 + d ;
               op_proper := G1|}.
     exists {| op_lower := x2 - d ;
               op_upper := y2 + d ;
               op_proper := G2|}.
     unfold d, d1, d2 in *; simpl.
     nra.
   - assert (G1 : x1 - d < y1 +d).
     {unfold d. unfold d2. lra. }
     assert (G2 : x2 - d < y2 +d).
     {unfold d. unfold d2. lra. }
     exists {| op_lower := x1 - d ;
               op_upper := y1 + d ;
               op_proper := G1|}.
     exists {| op_lower := x2 - d ;
               op_upper := y2 + d ;
               op_proper := G2|}.
     unfold d, d1, d2 in *; simpl.
     nra.
Defined.

Lemma lipschitz_is_continuous a b (f : bowtie a b) c :
  clop_inside c a -> cl_continuous_on f c.
Proof.
  cheat.
Qed.

Lemma cl_op_trans a b c :
  clop_inside a b -> opop_inside b c -> clop_inside a c.
Proof.
  cheat.
Qed.

Lemma inside_mul x y a1 a2 b O:
  cl_in x (closure a1) ->
  cl_in y (closure a2) ->
  separated a1 a2 ->
  clop_inside b O ->
  clop_inside (cl_scalar_mul (x - y) b) (op_multiply O (op_subtract a1 a2)).
Proof.
  intros x_in_a1 y_in_a2 sep_a1a2 [b_in_O1 b_in_O2].
  assert (xy_not_zero : x - y <> 0).
  { destruct a1, a2.
    unfold cl_in, closure, separated in * ; simpl in *.
    lra.
  }
  apply (cl_op_trans _ (op_scalar_mul (x - y) xy_not_zero O)).
  - destruct a1, a2, b, O.
    unfold clop_inside, cl_scalar_mul, op_scalar_mul, cl_in, separated in * ;
    simpl in *.
    handle_Rminmax ; nra.
  - destruct a1, a2, b, O.
    unfold opop_inside, cl_scalar_mul, op_scalar_mul, cl_in, separated in * ;
    simpl in *.
    admit. (* difficult? *)
Admitted.

(* Main theorems *)

Theorem main_theorem1 (a O : OpenInterval) (A : Bowtie a O):
  delta a (closure O) (dual_fun A).
Proof.
  destruct A as [A DA].
  unfold delta in *. simpl in *.
  intros x y x_in_a y_in_a.
  destruct (Req_dec x y).
   - destruct H.
     admit.
   - destruct (R_Hausdorff x y H) as [a' [b' [x_in_a' [y_in_b' sep_a'b']]]].
     destruct (point_directedness x a' a x_in_a' x_in_a) as [a'' [x_in_a'' [W_a''a' W_a''a]]].
     destruct (point_directedness y b' a y_in_b' y_in_a) as [b'' [y_in_b'' [W_b''b' W_b''a]]].
     unfold Delta in DA.
     destruct (DA a'' b'') as [d [e [Aa''d [Aa''e WI]]]]; try assumption.
     { now apply (separated_smaller a' b'). }
     assert (df_Ax_in_d : op_in (dual_fun A x) d).
     { admit.
     }
     assert (df_Ay_in_e : op_in (dual_fun A y) e).
     { admit. }
     assert (dfxy_in_de : op_in (dual_fun A x - dual_fun A y) (op_subtract d e)).
     { admit. }
     admit.
Admitted.

Lemma clop_in_trans x a b :
  cl_in x a -> clop_inside a b -> op_in x b.
Proof.
  admit.
Admitted.

Theorem main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval, clop_inside b O ->
  forall a0 : OpenInterval, clop_inside (closure a0) a -> Delta a0 O (Approx f).
Proof.
  intros O ins_bO c ins_c_a.
  intros a1 a2 wi_a1c wi_a2c sep_a1a2.
  assert (cont_f_a1 : cl_continuous_on f (closure a1)).
  { apply lipschitz_is_continuous.
    destruct a1, a, c; unfold clop_inside, well_inside in *.
    simpl in *.
    lra.
  }
  assert (cont_f_a2 : cl_continuous_on f (closure a2)).
  { apply lipschitz_is_continuous.
    destruct a2, a, c; unfold clop_inside, well_inside in *.
    simpl in *.
    lra.
  }
  destruct (cl_image f (closure a1) (cont_f_a1)) as [b1 imag_b1].
  destruct (cl_image f (closure a2) (cont_f_a2)) as [b2 imag_b2].
  destruct (scott_continuity b1 b2 (op_multiply O (op_subtract a1 a2)))
    as [c1 [c2 [b1_in_c1 [b2_in_c2 H]]]].
  { destruct imag_b1 as [H1 H2].
    destruct imag_b2 as [G1 G2].
    destruct b1 as [b1_m b1_M b1_prop].
    destruct b2 as [b2_m b2_M b2_prop].
    unfold cl_subtract, clop_inside, cl_in  in *; simpl in *.
    destruct (H2 b1_m) as [xm [xm_in_a1 Exm]]. { lra. }
    destruct (H2 b1_M) as [xM [xM_in_a1 ExM]]. { lra. }
    destruct (G2 b2_m) as [ym [ym_in_a2 Eym]]. { lra. }
    destruct (G2 b2_M) as [yM [yM_in_a2 EyM]]. { lra. }
    rewrite <- Exm.
    rewrite <- ExM.
    rewrite <- Eym.
    rewrite <- EyM.
    split.
    - assert (K : op_in (f xm - f yM) (op_multiply O (op_subtract a1 a2))).
      { apply (clop_in_trans _ (cl_scalar_mul (xm - yM) b)).
        - admit. (* apply f, then it's easy *)
        - now apply inside_mul.
      }
      apply K.
    - admit. (* symmetric to the above. *)
  }
  exists c1, c2.
  repeat split.
  - apply (Rlt_le_trans _ (cl_lower b1)).
    + apply b1_in_c1.
    + now apply imag_b1.
  - apply (Rle_lt_trans _ (cl_upper b1)).
    + now apply imag_b1.
    + apply b1_in_c1.
  - apply (Rlt_le_trans _ (cl_lower b2)).
    + apply b2_in_c2.
    + now apply imag_b2.
  - apply (Rle_lt_trans _ (cl_upper b2)).
    + now apply imag_b2.
    + apply b2_in_c2.
  - apply H.
  - apply H.
Admitted.




 (*
  intros [O1 O2 Proper_O] [Inside_bO] [a01 a02 Proper_a0] [Inside_a0a_1 Inside_a0a_2]
         [c1 c2 Proper_c] [d1 d2 Proper_d] [WI_ca1 WI_ca2] [WI_da1 WI_da2] Separated_cd.
  destruct a as [a1 a2 Proper_a].
  destruct b as [b1 b2 Proper_b].
  destruct f as [f Lipschitz_f].
  unfold op_in, cl_in in Lipschitz_f.
  unfold Delta, Approx.
  unfold separated, well_inside, inside in *.
  unfold cl_in, op_in.
  simpl in *. *)
  intros.
  admit.
Admitted.

Theorem strong_main_theorem1 (a O : OpenInterval) (A : Bowtie a O):
  exists b,clop_inside b O /\ strong_delta a b (dual_fun A).
Admitted.

Theorem strong_main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval,
   clop_inside b O ->
    StrongDelta a O (Approx f).
Proof.
Admitted.
