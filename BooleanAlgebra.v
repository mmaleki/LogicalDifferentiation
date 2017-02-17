Structure BooleanAlgebra := {
 carrier :> Set; (* Coercion *)
 and : carrier -> carrier-> carrier;
 or : carrier -> carrier -> carrier;
 neg : carrier -> carrier;
 zero : carrier;
 one : carrier;
 and_p_0 : forall p, and p zero = zero;
 and_p_1 : forall p, and p one = p;
 and_p_Np : forall p, and p (neg p) = zero;
 and_p_p : forall p, and p p = p;
 neg_0 : neg zero = one;
 neg_neg : forall p, neg (neg p) = p;
 or_p_1 : forall p, or p one = one;
 or_p_0 : forall p, or p zero = p;
 or_p_Np : forall p, or p (neg p) = one;
 or_p_p : forall p, or p p = p;
 neg_or : forall p q, neg (or p q) = and (neg p) (neg q);
 neg_and : forall p q, neg (and p q) = or (neg p) (neg q);
 and_or : forall p q r, and p (or q r) = or (and p q) (and p r);
 or_and : forall p q r, or p (and q r) = and (or p q) (or p r);
 and_p_qr : forall p q r, and p (and q r) = and (and p q) r;
 or_p_qr : forall p q r, or p (or q r) = or (or p q) r;
 and_pq : forall p q, and p q = and q p;
 or_pq : forall p q, or p q = or q p
}.

Notation "p & q" := (and _ p q) (at level 40, left associativity).
Notation "p | q" := (or _ p q) (at level 50, left associativity).
Notation "! p" := (neg _ p) (at level 20).
Notation "1" := (one _).
Notation "0" := (zero _).

Structure Hom (A B : BooleanAlgebra) := {
  action :> A -> B;
  mor_and: forall x y, action (x & y) = action x & action y;
  mor_or: forall x y, action (x | y) = action x | action y;
  mor_neg: forall x, action (! x) = !(action x)
}.

Lemma id (B : BooleanAlgebra) : Hom B B.
Proof.
  refine {| action := fun x => x |} ; reflexivity.
Defined.

Definition compose A B C :
  Hom B C -> Hom A B -> Hom A C.
Proof.
  intros g f.
  refine {| action := fun x => g (f x) |}.
  -intros.
  rewrite->mor_and.
  rewrite->mor_and.
  reflexivity.
  -intros. rewrite->mor_or. rewrite->mor_or. reflexivity.
  -intros. rewrite->mor_neg. rewrite ->mor_neg. reflexivity.
Defined.



Notation "g 'o' f" := (compose _ _ _ g f) (at level 65, left associativity).


Lemma Hom_0 (A B : BooleanAlgebra) (f : Hom A B) :
  f 0 = 0.
Proof.
  rewrite <- (and_p_Np A 0).
  rewrite mor_and.
  rewrite mor_neg.
  rewrite and_p_Np.
  reflexivity.
Qed.

Lemma and_pq_r (B : BooleanAlgebra) (p q r : B) :
  (p | q) & r = p & r | q & r.
Proof.
 rewrite <-and_pq.
 rewrite->and_or.
 rewrite->and_pq.
 rewrite->or_pq.
 rewrite->and_pq.
 rewrite->or_pq.
 reflexivity.
Qed.




Lemma neg_1 (L : BooleanAlgebra) : ! 1 = (0 : L).
Proof.
  rewrite <- neg_0.
  rewrite -> neg_neg.
  reflexivity.
Qed.

Definition Two : BooleanAlgebra.
Proof.
  (* We use bool and its operations from the standard library *)
  refine {| carrier := bool ;
            and := andb ;
            or := orb ;
            neg := negb ;
            zero := false ;
            one := true
         |} ; repeat (intros [|]) ; reflexivity.
Defined.

Definition pointwise0 {B : Set} (c : B) (I : Set) :
  (I -> B) :=
  fun i => c.

Definition pointwise1 {B : Set} (op : B -> B) (I : Set) :
  (I -> B) -> (I -> B) :=
  fun f i => op (f i).

Definition pointwise2 {B : Set} (op : B -> B -> B) (I : Set) :
  (I -> B) -> (I -> B) -> (I -> B) :=
  fun f g i => op (f i) (g i).

(* Function extensionality. *)
Axiom funext :
  forall (X : Type) (P : X -> Type) (f g : (forall x, P x)),
    (forall x, f x = g x) -> f = g.

(* Function extensionality for simple types. *)
Lemma funext_simple (X Y : Type) (f g : X -> Y) :
  (forall x, f x = g x) -> f = g.
Proof.
  apply (funext X (fun x => Y)).
Defined.

Definition Power (B : BooleanAlgebra) (I : Set) : BooleanAlgebra.
Proof.
  refine {| carrier := I -> B ;
            and := pointwise2 (and B) I ;
            or := pointwise2 (or B) I ;
            neg := pointwise1 (neg B) I ;
            zero := pointwise0 (zero B) I ;
            one := pointwise0 (one B) I
         |} ;
  (intros ; apply funext_simple ; intro i ; unfold pointwise0, pointwise1, pointwise2).
  - apply and_p_0.
  - apply and_p_1.
  - apply and_p_Np.
  - apply and_p_p.
  - apply neg_0.
  - apply neg_neg.
  - apply or_p_1.
  - apply or_p_0.
  - apply or_p_Np.
  - apply or_p_p.
  - apply neg_or.
  - apply neg_and.
  - apply and_or.
  - apply or_and.
  - apply and_p_qr.
  - apply or_p_qr.
  - apply and_pq.
  - apply or_pq.
Defined.

Inductive Colors := Red | Green | Blue.

(* Boolean algebra with eight elements. *)
Definition EightBA := Power Two Colors.

(* The opposite algebra. *)
Definition Opposite (B : BooleanAlgebra) : BooleanAlgebra.
Proof.
  refine {| carrier := carrier B ;
            and := or B ;
            or := and B ;
            neg := neg B ;
            one := zero B ;
            zero := one B
         |}.
intros.
-apply or_p_1.
-apply or_p_0.
-apply or_p_Np.
-apply or_p_p.
-apply neg_1.
-apply neg_neg.
-apply and_p_0.
-apply and_p_1.
-apply and_p_Np.
-apply and_p_p.
-apply neg_and.
-apply neg_or.
-apply or_and.
-apply and_or.
-apply or_p_qr.
-apply and_p_qr.
-apply or_pq.
-apply and_pq.
Defined.
