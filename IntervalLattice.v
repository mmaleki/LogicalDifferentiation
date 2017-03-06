(* Require Setoid. *)
Require Import QArith.
Require Import QArith.Qminmax.

Require Import Lattice.
Require Import ProximityLattice.

Definition I(p q : Q):= {x : Q | p < x /\ x < q}.
Check I.

(* The definition of a rational interval, actually, the data
   which determines it: lower bound, upper bound, proof that
   lower < upper. *)

Inductive rat : Type :=
  | RatBottom : rat
  | RatProper : forall (p q : Q), (p < q) -> rat
  | RatTop : rat.

Definition rat_and (i j : rat) : rat.
Proof.
  destruct i as [_ | p q H | _].
  - (* i = RatBottom *)
    exact RatBottom.
  - (* i = RatProper p q H. *)
    destruct j as [_ | p' q' H' | _].
    + (* j = RatBottom *)
      exact RatBottom.
    + { (* j = RatProper p' q' H' *)
        pose (p'' := Qmax p p').
        pose (q'' := Qmin q q').
        destruct (Qlt_le_dec p'' q'') as [H1|H2].
        - exact (RatProper p'' q'' H1).
        - exact RatBottom.
      }
    + (* j = RatTop *)
      exact (RatProper p q H).
  - (* i = RatTop *)
    exact j.
Defined.

Definition rat_or (i j : rat) : rat.
Admitted.

(* We will cheat. WARNING WARNING WE ARE ASSUMING AN INCONSISTENCY. *)
Axiom cheating : forall (A : Type), A.

Definition interval_lattice: Lattice.
Proof.
  refine {|
      lt_carrier := rat ;
      lt_and := rat_and ;
      lt_or := rat_or ;
      lt_zero := RatBottom ;
      lt_one := RatTop
  |}.
  - {
      intros i j.
      destruct i; destruct j ; auto.
      rename q0 into H1.
      rename q2 into H2.
      rename p0 into p'.
      rename q1 into q'.
      apply cheating.
    }
  - apply cheating.
  - { intros i j k.
      destruct i; destruct j; destruct k; auto.
      - unfold rat_and.
        destruct (Qlt_le_dec (Qmax p p0) (Qmin q q1)) ; auto.
      - unfold rat_and.
        destruct (Qlt_le_dec (Qmax p0 p1) (Qmin q1 q3)) ; auto.
        + destruct (Qlt_le_dec (Qmax p p0) (Qmin q q1)) ; auto.
          * apply cheating. (* need to figure out how to do reqwrite by associativity of min and max. *)
          * apply cheating. (* we need to convince Coq that the left H1 case happens. *)
        + destruct (Qlt_le_dec (Qmax p p0) (Qmin q q1)) ; auto.
          apply cheating.
      - unfold rat_and.
        destruct (Qlt_le_dec (Qmax p p0) (Qmin q q1)) ; auto.
    }
  - apply cheating.
  - apply cheating.
  - apply cheating.
  - apply cheating.
  - { intro i.
      destruct i ; auto.
    }
  - apply cheating.
  - apply cheating.
Defined.
  
Definition rat_approx (i j : rat) :=
  match i with
  | RatBottom => True
  | RatProper p q H =>
    match j with
      | RatBottom => False
      | RatProper p' q' H' => p' < p /\ q < q'
      | RatTop => True
    end
  | RatTop => False
  end.

Definition interval_proximity_lattice : ProximityLattice.
Proof.
  refine {|
      plt_lattice := interval_lattice ;
      plt_approx := rat_approx
    |}.
  - { intros i j k H1 H2.
      destruct i ; destruct j ; destruct k ; auto.
      - elim H1.
      - simpl in H1; simpl in H2. admit. (* exercise *)
      - elim H2.
    }
  - apply cheating.
  - apply cheating.
  - apply cheating.
  - { intros i.
      apply cheating. (* we should delete the axiom "a < 1" from ProximityLattice. *)
    }
  - { 
      intros i j H.
      destruct i, j.
      - admit.
      - admit.
      - admit.
      - elim H.
      - admit.
      - admit.
      - elim H.
      - elim H.
      - elim H.
    }
Admitted.
