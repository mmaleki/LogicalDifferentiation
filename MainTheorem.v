(*Require Import QArith.
Require Import QArith.Qreals.*)
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Lra.

Local Open Scope R_scope.

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

Definition separated (a b : OpenInterval) :=
  op_upper a < op_lower b \/ op_upper b < op_lower a.

Definition overlap (a b : OpenInterval) :=
  op_lower b < op_upper a.

(* Note: this join only really works when applied to overlapping intervals. *)
Definition join (a b : OpenInterval) : OpenInterval.
Proof.
  refine {| op_lower := Rmin (op_lower a) (op_lower b) ;
            op_upper := Rmax (op_upper a) (op_upper b) |}.
  destruct a as [a1 a2 Pa].
  destruct b as [b1 b2 Pb].
  unfold Rmin, Rmax; simpl.
  destruct (Rle_dec a1 b1) ; destruct (Rle_dec a2 b2) ; lra.
Defined.

Definition closure : OpenInterval -> ClosedInterval.
Proof.
  intro a.
  refine {| cl_lower := op_lower a ; cl_upper := op_upper a |}.
  apply Rlt_le, op_proper.
Defined.

Definition inside (a : ClosedInterval) (b : OpenInterval) :=
  op_lower b < cl_lower a /\ cl_upper a < op_upper b.

Definition inside_open (a : OpenInterval) (b : ClosedInterval) :=
  cl_lower b <= op_lower a /\ op_upper a <= cl_upper b.


Definition well_inside (a b : OpenInterval) :=
  op_lower b < op_lower a /\ op_upper a < op_upper b.

(* Multiplication of a closed interval by a scalar. *)
Definition scalar_mul (x : R) (a : ClosedInterval) : ClosedInterval.
Proof.
  refine {| cl_lower := Rmin (x * cl_lower a) (x * cl_upper a) ;
            cl_upper := Rmax (x * cl_lower a) (x * cl_upper a) |}.
  now apply Rminmax.
Defined.

Definition cl_in (x : R) (a : ClosedInterval) :=
  cl_lower a <= x /\ x <= cl_upper a.

Definition op_in (x : R) (a : OpenInterval) :=
  op_lower a < x /\ x < op_upper a.

(* Substraction of open intervals. *)
Definition op_subtract (a b : OpenInterval) : OpenInterval.
Proof.
  refine {| op_lower := op_lower a - op_upper b ;
            op_upper := op_upper a - op_lower b |}.
  destruct a, b.
  simpl in *.
  lra.
Defined.

Definition op_multiply (a b : OpenInterval) : OpenInterval.
Proof.
  destruct a as [a1 a2 ?].
  destruct b as [b1 b2 ?].
  refine {| op_lower := Rmin (Rmin (a1 * b1) (a1 * b2)) (Rmin (a2 * b1) (a2 * b2)) ;
            op_upper := Rmax (Rmax (a1 * b1) (a1 * b2)) (Rmax (a2 * b1) (a2 * b2)) |}.
  unfold Rmin, Rmax.
  destruct (Rle_dec (a1 * b1) (a1 * b2)), (Rle_dec (a2 * b1) (a2 * b2)) ; simpl.
  - destruct (Rle_dec (a1 * b1) (a2 * b1)), (Rle_dec (a1 * b2) (a2 * b2)) ; simpl ; nra.
  - destruct (Rle_dec (a1 * b1) (a2 * b2)), (Rle_dec (a1 * b2) (a2 * b1)) ; simpl ; nra.
  - destruct (Rle_dec (a1 * b2) (a2 * b1)), (Rle_dec (a1 * b1) (a2 * b2)) ; simpl ; nra.
  - destruct (Rle_dec (a1 * b2) (a2 * b2)), (Rle_dec (a1 * b1) (a2 * b1)) ; simpl ; nra.
Defined.

Definition Approx (f : R -> R) (a O : OpenInterval) :=
  forall x, cl_in x (closure a) -> op_in (f x) O.

Definition delta (a : OpenInterval) (b : ClosedInterval) (f : R -> R) :=
   forall x y : R, op_in x a -> op_in y a ->
                cl_in (f x - f y) (scalar_mul (x - y) b).

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
     inside_open b' b ->
     forall x y : R, op_in x a' -> op_in y a' ->
                     cl_in (f x - f y) (scalar_mul (x - y) (closure b')).

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
                cl_in (bow_map x - bow_map y) (scalar_mul (x - y) b)
}.

Structure Bowtie (a O : OpenInterval)  := {
  Bow_map :> OpenInterval -> OpenInterval -> Prop ;
  Bow_lipschitz : Delta a O Bow_map
}.

Structure ApproximableMap : Type := {
  app_map :> OpenInterval -> OpenInterval -> Prop ; (* this is our A *)
  app_monotone : forall a b c, app_map a b -> well_inside b c -> app_map a c ;
  app_total : forall a, exists b, app_map a b ; (* imagine: a A 1 *)
  app_disjoint : forall a b c, separated b c -> ~ (app_map a b /\ app_map a c) ; (* imagine: ~ (a A 0) *)
  app_converge :
    forall a b c, overlap b c ->
    app_map a (join b c) ->
    exists a1 a2, overlap a1 a2 /\ well_inside a (join a1 a2) /\
                  app_map a1 b /\ app_map a2 c
  (* exercise: define this so that you can prove approximable_filter_maps below. *)
}.

(* A completely prime filter w.r.t. to the well-inside order. *)
Structure CompleteFilter : Type := {
  cf_filter :> OpenInterval -> Prop ;
  cf_monotone : forall a b, well_inside a b -> cf_filter a -> cf_filter b ;
  cf_inhabited : exists a, cf_filter a ; (* imagine: (-inf, inf) is in cf_filter *)
  cf_disjoint : forall a b, separated a b -> ~ (cf_filter a /\ cf_filter b) ; (* imagine: empty set is not in cf_filter *)
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
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition point2filter (x : R) : CompleteFilter.
Proof.
  refine {| cf_filter := fun a => op_in x a |}.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma filter2point (F : CompleteFilter) : R.
Admitted. (* expect to use excluded middle or something strange from the R library. *)

Definition dual_fun (A : ApproximableMap) (x : R) :=
  filter2point (filter_map A (point2filter x)).

Definition interpol (a : ClosedInterval) (b : OpenInterval) :
  inside a b -> exists b' : OpenInterval, inside a b' /\ well_inside b' b.
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
    unfold inside in *.
    unfold op_lower in *.
    unfold cl_lower in *.
    unfold cl_upper in *.
    unfold op_upper in *.
    unfold well_inside in *.
    unfold c1, c2 in *.
    simpl.
    nra.
Defined.

Lemma Bowtie2Approximable {a O} : Bowtie a O -> ApproximableMap.
Proof.
  intro A.
  refine {| app_map := A |}.
   - admit.
   - admit.
   - admit.
   - admit.
Admitted.

(* Main theorems *)

Theorem main_theorem1 (a O : OpenInterval) (A : Bowtie a O):
  delta a (closure O) (dual_fun (Bowtie2Approximable A)).
Proof.
Admitted.


Theorem main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval, inside b O ->
  forall a0 : OpenInterval, inside (closure a0) a -> Delta a0 O (Approx f).
Proof.
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
  intros c d Ica0 Ida0 Sep_cd.
  admit.
Admitted.

Theorem strong_main_theorem1 (a O : OpenInterval) (A : Bowtie a O):
  exists b, inside b O /\ strong_delta a b (dual_fun (Bowtie2Approximable A)).
Admitted.

Theorem strong_main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval,
    inside b O ->
    StrongDelta a O (Approx f).
Proof.
Admitted.
