Require Import Cortouche.Plugin.

Parameter typ: Type.
Parameter exp: Type.
Parameter is_foo: exp -> typ -> Prop.
Parameter well_typed: exp -> typ -> Prop.
Parameter Vec: nat -> Set.

Lemma test1: 
  forall t e1 e2 , 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 e3 **.
  exact (\< is_foo e1 t \>).
Qed.

Lemma test2: 
  forall t e1 e2, 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 **.
  exact (\< is_foo e1 _ \>).
Qed.

Print test2.

Lemma test3: 
  forall t, forall e1 e2 e3 : exp, 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 e3 **. 
  Fail exact (\< is_foo e2 t \>).
Abort.

Lemma test4: 
  forall t, forall e1 e2 e3 : exp, 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 e3 **. 
  Fail exact (\< is_foo e3 t \>).
Abort.

Lemma test5: 
  forall n, Vec n -> Vec n -> Vec n.
Proof.
  intros n **.
  Fail exact (\< Vec _ \>).
Abort.
