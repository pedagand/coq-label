Require Import Cortouche.Plugin.
Require Import Coq.Reals.Ranalysis.

Import Rdefinitions.
Import RIneq.
Open Scope R_scope.

Definition strict_increasing_interval f Imin Imax :=
  forall a b : R, Imin <= a -> a < b -> b <= Imax -> f a < f b.
Notation "f 'strictly' 'increasing' 'on' [ Imin , Imax ]" :=
  (strict_increasing_interval f Imin Imax) (at level 70).

(** This proof is inspired by the informal version in:
      "How to write a 21st century proof"
      Lamport L 
      Journal of Fixed Point Theory and Applications
      2012 vol: 11 (1) pp: 43-63
 *)

Section Spivak.

  Variable f : R -> R.
  Hypothesis f_derivable : derivable f.
  Variables Imin Imax : R.

  Definition f' := fun x => derive_pt f x (f_derivable x).

  Corollary spivak (H : forall x : R, Imin <= x <= Imax -> f' x > 0) :
    f strictly increasing on [Imin, Imax].
  Proof.
    intros a b **.

    assert (exists x : R, f b - f a = f' x * (b - a) /\ a < x < b)
      as (x & ? & ? & ?)
        by exact (MVT_cor1 _ _ _ f_derivable (\< a < b \>)).
    
    assert (forall x : R, a <= x <= b -> f' x > 0). {
      clear dependent x; intros x (? & ?).
      assert (Imin <= x <= Imax) by (split; eapply Rle_trans; eassumption).
      exact (H _ (\< _ <= x <= _ \>)).
    }
    clear H.

    assert (f b - f a > 0). {
      enough (f' x * (b - a) > 0) by (now rewrite (\< f b - f a = _ \>)).
      
      assert (f' x > 0). {
        assert (a <= x <= b) by (split; apply Rlt_le; assumption).
        exact ((\< forall _ _, f' _ > 0 \>) _ (\< _ <= x <= _ \>)).
      }

      assert (b - a > 0) by exact (Rgt_minus _ _ (\< a < b \>)).
      exact (Rmult_gt_0_compat _ _ (\< f' x > 0 \>) (\< b - a > 0 \>)).
    }

    exact (Rminus_gt _ _ (\< _ > 0 \>) : f a < f b).
  Qed.

End Spivak.

(* Local Variables: *)
(* company-coq-local-symbols: (("(\\<" . ?⟨) ("\\>)" . ?⟩)) *)
(* End: *)