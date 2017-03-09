(* Require Setoid. *)
Require Import QArith.
Require Import QArith.Qminmax.
Require Import Psatz.
Require Import Lqa.

Require Import Lattice.
Require Import ProximityLattice.


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
Proof.
  destruct i as [ | p q H | ].
  - exact j.
  - destruct j as [_ | p' q' H' | _].
    + exact (RatProper p q H).
    + { pose (p'' := Qmin p p' ).
       pose (q'' := Qmax q q' ).
       destruct (Qlt_le_dec p'' q'') as [H1 | H2].
         -exact (RatProper p'' q'' H1).
         -exact RatBottom.

      }
    + exact (RatTop).
  - exact (RatTop).
Defined.


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
     (*intros i j. 
      destruct i as [_ | p q H | _].
      destruct j as [_ | p' q' H'| _].
      auto.
      apply cheating.*)
      intros i j.
      destruct i ; destruct j ; auto.
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

(* Check plt_trans. *)

Lemma trans:forall p q r :Q,p < q /\ q < r -> p < r.
Proof.
intros.
destruct H.
apply (Qlt_le_trans p q r).
apply H.
apply Qlt_le_weak.
apply H0.
Defined.

(* Check plt_interpolate. *)
(* Check  Qplus_lt_l. *)

Lemma mean_value_l: forall x y, x < y -> ((y + x) * (1#2))%Q < y.
Proof.
  intros.
  lra.
Qed.

Lemma mean_value_r: forall x y, x < y -> x < ((x+y) * (1#2))%Q.
Proof.
  intros.
  lra.
Qed.

Definition interval_proximity_lattice : ProximityLattice.
Proof.
  refine {|
      plt_lattice := interval_lattice ;
      plt_approx := rat_approx
    |}.
  - { intros i j k H1 H2.
      destruct i as [_ | p q H | _]; destruct j as [_ | p' q' H'| _]
      ; destruct k as [_ | p'' q'' H''| _] ; auto.
      - elim H1.
      - simpl in H1; simpl in H2. simpl. 
         destruct H1. destruct H2. split. eapply trans. split.
         apply H2. apply H0. eapply trans. split. apply H1. apply H3.  (* exercise *)
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
      - now exists RatBottom.
      - now exists RatBottom.
      - now exists RatBottom.
      - elim H.
      - rename q0 into G, p0 into p', q1 into q', q2 into G'.
        destruct H.
        pose (p'':= (p+p') * (1#2)).
        pose (q'':= (q+q') * (1#2)).
        assert (G'' : p'' < q'').
        { unfold p'', q''. lra. }
        exists (RatProper p'' q'' G'').
        unfold p'', q'' in *; simpl. lra.
      - destruct H.
        assert (G' : p-1 < q+1) by lra.
        exists (RatProper (p-1) (q+1) G').
        simpl ; lra.
      - elim H.
      - elim H.
      - elim H.
    }
Defined.






