Structure Group :={
g_carrier :> Type;
g_operation : g_carrier -> g_carrier -> g_carrier;
g_inverse : g_carrier -> g_carrier;
g_zero : g_carrier;
g_abelian : forall x y, g_operation x y = g_operation y x; 
g_identity : forall x , g_operation x g_zero = x;
g_inverse_axiom : forall x, g_operation x (g_inverse x) = g_zero;
g_associat : forall x y z ,
             g_operation (g_operation x y) z = g_operation x (g_operation y z);
g_product : forall x y z, x =y -> x * z = y * z
}.

Notation " x '*' y" := (g_operation _ x y) (at level 40, left associativity).
Notation "'e'" := (g_zero _).
Notation "! x" := (g_inverse _ x) (at level 20).

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

Lemma plt_approx_or_r: forall(G : Group ) ( x y z : G), x * z = y * z -> x = y.
Proof.
  intros.
  rewrite -> g_product.






