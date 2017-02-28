Require Import Arith.
Require Import List.

Structure Group :={
g_carrier :> Type;
g_operation : g_carrier -> g_carrier -> g_carrier;
g_inverse : g_carrier -> g_carrier;
g_zero : g_carrier;
g_abelian : forall x y, g_operation x y = g_operation y x; 
g_identity : forall x , g_operation x g_zero = x;
g_inverse_axiom : forall x, g_operation x (g_inverse x) = g_zero;
g_associat : forall x y z ,
             g_operation (g_operation x y) z = g_operation x (g_operation y z)
}.

Notation " x '*' y" := (g_operation _ x y) (at level 40, left associativity).
Notation "'e'" := (g_zero _).
Notation "! x" := (g_inverse _ x) (at level 20).

Lemma g_product : forall (G : Group) (x y z : G), x =y -> x * z = y * z.
intros.
rewrite H.
reflexivity.
Qed.

Lemma g_reg_r : forall (G : Group) (x y z : G), x * z = y * z -> x = y.
Proof.
intros.
rewrite <- (g_identity _ x).
rewrite <- (g_identity _ y).
rewrite <- (g_inverse_axiom _ z).
repeat rewrite <- g_associat.
rewrite H.
reflexivity.

Lemma first : forall (G: Group), e * e = (e : G).
Proof.
  intros.
  apply g_identity.
Defined.

Lemma left_identity : forall (G: Group) (x : G) , e * x = x.
Proof.
  intros.
  rewrite <- g_abelian.
  apply g_identity.
Defined.

Lemma left_inverse : forall (G : Group) (x : G) , ! x * x = e.
Proof.
   intros.
   rewrite <- g_abelian.
   apply g_inverse_axiom.
Defined.

Structure GroupHom (A B : Group):={
g_hom :> A ->B;
g_hom_dist : forall x y, g_hom (x * y) = (g_hom x) * (g_hom y);
(*g_hom_idn : g_hom e = e;*)
g_hom_inv : forall x, g_hom (! x) = ! (g_hom x)
}.

Lemma g_0_0 (A B:Group)(g: GroupHom A B): g e = e.
Proof.

   rewrite <- (g_inverse_axiom _ e).
   rewrite -> g_hom_dist.
   rewrite -> g_hom_inv.
   apply g_inverse_axiom.
Defined.

Definition id_hom (A:Group): GroupHom A A.
Proof.
   refine{|g_hom := fun x => x|}.
   reflexivity. reflexivity.
Defined.

Definition comp (A B C : Group) : GroupHom B C -> GroupHom A B -> GroupHom A C.
Proof.
   intros g f.
   refine {| g_hom := fun x => g (f x)|}.
   -intros. rewrite -> g_hom_dist. rewrite ->g_hom_dist. reflexivity.
   -intros. rewrite -> g_hom_inv. apply g_hom_inv.
Defined.

Print Nat.modulo.
Print Nat.divmod.

Check proj1_sig.
Eval compute in (Nat.modulo 6 2).


(*Lemma s_n: forall n, n < S n.
Proof.
   induction n. trivial.
Admitted.
*)


Definition Z(n:nat):Group.
Proof.

   refine {|g_carrier:={m:nat|m<n} |}.
+ intros x y.
  exists (Nat.modulo (proj1_sig x + proj1_sig y) n).

  apply Nat.mod_bound_pos.
  induction (proj1_sig x). simpl. induction (proj1_sig y). reflexivity.
  rewrite -> IHn0. induction n0.
 Admitted.









