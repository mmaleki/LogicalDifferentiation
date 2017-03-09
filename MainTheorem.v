Require Import QArith.
Require Import QArith.Qreals.
Require Import Reals.
Require Import Psatz.

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

Definition closure : OpenInterval -> ClosedInterval.
Proof.
  intro a.
  refine {| cl_lower := op_lower a ; cl_upper := op_upper a |}.
  apply Rlt_le, op_proper.
Defined.


Definition interior : ClosedInterval -> OpenInterval.
Proof.
  intro a.
  refine {| op_lower := cl_lower a ; op_upper := cl_upper a |}.
Admitted.

Definition inside (a : ClosedInterval) (b : OpenInterval) :=
  op_lower b < cl_lower a /\ cl_upper a < op_upper b.

Definition inside_open (a :OpenInterval ) (b : ClosedInterval) :=
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

Structure bowtie (a : OpenInterval) (b : ClosedInterval) := {
  bow_map :> R -> R ;
  bow_lipschitz :
    forall x y : R, op_in x a -> op_in y a ->
                cl_in (bow_map x - bow_map y) (scalar_mul (x - y) b)
}.

Definition Approx (f : R -> R) (a O : OpenInterval) :=
  forall x, cl_in x (closure a) -> op_in (f x) O.

Definition delta (a : OpenInterval) (b : ClosedInterval) (map : R -> R) :=
   forall x y : R, op_in x a -> op_in y a ->
                cl_in (map x - map y) (scalar_mul (x - y) b).

Definition Delta (a O : OpenInterval) (A : OpenInterval -> OpenInterval -> Prop) :=
  forall a1 a2,
    well_inside a1 a ->
    well_inside a2 a ->
    separated a1 a2 ->
    exists a1' a2',
      A a1 a1' /\ A a2 a2' /\
      well_inside (op_subtract a1' a2') (op_multiply O (op_subtract a1 a2)).


Structure Bowtie (a O: OpenInterval)  := {
  Bow_map :>  OpenInterval ->  OpenInterval -> Prop ;
  Bow_lipschitz :
    forall a1 a2,
    well_inside a1 a ->
    well_inside a2 a ->
    separated a1 a2 ->
    exists a1' a2',
      Bow_map a1 a1' /\ Bow_map a2 a2' /\
      well_inside (op_subtract a1' a2') (op_multiply O (op_subtract a1 a2))
}.

Definition dual_fun (A:OpenInterval ->  OpenInterval -> Prop) (x : R) :=
  x.

Check dual_fun.


Theorem main_theorem1 (a O : OpenInterval)(A :Bowtie a O): delta  a (closure O)(dual_fun A).
Proof.
Admitted.

Theorem main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval, inside b O ->
  forall a0 :OpenInterval, inside (closure a0) a  -> Delta a0 O (Approx f).
Proof.
  intros. (*[O1 O2 Proper_O] [Inside_bO] [c1 c2 Proper_c] [d1 d2 Proper_d] [WI_ca1 WI_ca2] [WI_da1 WI_da2] Separated_cd.*)
  destruct a as [a1 a2 Proper_a].
  destruct b as [b1 b2 Proper_b].
  destruct f as [f Lipschitz_f].
  unfold op_in, cl_in in Lipschitz_f.
  unfold Delta, Approx.
  unfold separated, well_inside in *.
  unfold cl_in, op_in.
  simpl in *.
  admit.
Admitted.

Definition strong_delta (a : OpenInterval) (b : ClosedInterval) (map : R -> R) :=
   exists a' , well_inside a a' ->
   exists b' , inside_open (interior b') b ->
   forall x y : R, op_in x a' -> op_in y a' ->
                cl_in (map x - map y) (scalar_mul (x - y) b').

Definition StrongDelta (a O : OpenInterval) (A : OpenInterval -> OpenInterval -> Prop) :=
   exists a', well_inside a a' -> 
   exists O', well_inside O' O ->
   forall a1 a2,
    well_inside a1 a' ->
    well_inside a2 a' ->
    separated a1 a2 ->
    exists a1' a2',
      A a1 a1' /\ A a2 a2' /\
      well_inside (op_subtract a1' a2') (op_multiply O' (op_subtract a1 a2)).

Theorem strong_main_theorem1 (a O : OpenInterval)(A :Bowtie a O): exists b, inside b O /\ strong_delta  a b(dual_fun A).

Theorem strong_main_theorem2 (a : OpenInterval) (b : ClosedInterval) (f : bowtie a b) :
  forall O : OpenInterval, inside b O ->
  StrongDelta a O (Approx f).
Proof.
Admitted.



