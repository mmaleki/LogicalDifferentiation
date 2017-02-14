Structure BooleanAlgebra :={
 L :> Set;
  and : L ->L-> L ;
  or : L -> L -> L;
  neg : L -> L;
   zero:>L;
  one:>L;
  A1 : forall p, and p zero = zero;
  A2 : forall p, and p one = p;
  A3 : forall p, and p (neg p)=zero;
  A4 : forall p, and p p = p;
  A5 : neg zero = one;
  A6 : forall p, neg (neg p)=p;
  B1 : forall p, or p one = one;
  B2 : forall p, or p zero = p;
  B3 : forall p, or p (neg p) = one;
  B4 : forall p, or p p = p;
  Demorgan1: forall p q, neg (or p q) = and (neg p) (neg q);
  Demorgan2: forall p q, neg (and p q) = or (neg p) (neg q);
  Distrib1: forall p q r, and p (or q r) = or (and p q) (and p r);
  Distrib2: forall p q r, or p (and q r) = and (or p q) (or p r);
  Assoc1: forall p q r, and p (and q r) = and (and p q) r;
  Assoc2: forall p q r, or p (or q r) = or (or p q) r
}.

Lemma doublnegation(L:BooleanAlgebra):p:L,neg one=zero.



