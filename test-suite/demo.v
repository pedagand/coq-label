Require Import Label.Plugin.

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
  (* because this is the right hypothesis *)
Abort.

Lemma test4: 
  forall t, forall e1 e2 e3 : exp, 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 e3 **. 
  Fail exact (\< is_foo e3 t \>).
  (* because there is no such assumption *)
Abort.


Lemma test41: 
  forall t, forall e1 e2 e3 : exp, 
    is_foo e1 t -> is_foo e2 t -> is_foo e1 t.
Proof.
  intros t e1 e2 e3 **. 
  Fail exact (\< is_foo _ _ \>).
  (* because this pattern is ambiguous, it could match any of 
     [is_foo e1 t] and [is_foo e2 t] *)
Abort.

Lemma test5: 
  forall n, Vec n -> Vec n -> Vec n.
Proof.
  intros n **.
  Fail exact (\< Vec _ \>).
  (* because [Vec] is proof-relevant *)
Abort.

Lemma test6: 
  (forall e t, is_foo e t) -> forall e t, is_foo e t.
Proof.
  intro H.
  Fail exact (\< is_foo _ _ \>). 
  (* because [is_foo] is hidden under some [forall]s *)

  exact (\<< is_foo _ _ \>>).
Qed.

Lemma test7:
  (forall e t, is_foo e t) -> forall e t, is_foo e t.
Proof.
  intro H.
  Fail exact (\<< forall t, is_foo _ t \>>).
  (* because of a limitation: we do not search for partially applied hypothesis *)
Abort.