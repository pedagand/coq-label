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

  Notation "'D[' f ']' x" := 
    (derive_pt f x%R (f_derivable x%R)) 
      (at level 10, x at next level).

  Corollary spivak (H : forall x : R, Imin <= x <= Imax -> D[ f ] x > 0) :
    f strictly increasing on [Imin, Imax].
  Proof.
    intros a b **.

    assert (exists x : R, f b - f a = D[ f ] x * (b - a) /\ a < x < b)
      by auto using MVT_cor1, (\< a < b \>) .
    decompose record (\< exists _, _ = _ /\ _ < _ < _\>) .

    assert (forall x : R, a <= x <= b -> D[ f ] x > 0).
    {
      clear dependent x; intros x [? ?].
      assert (Imin <= x <= Imax) 
        by eauto using Rle_trans, (\< a <= x \>) , (\< x <= b \>) .
      auto using (\<< D[ f ] _ > 0 \>>) , (\< Imin <= x <= Imax \>) .
    }

    assert (f b - f a > 0).
    {
      enough (D[ f ] x * (b - a) > 0) 
        by now rewrite (\< f b - f a = _ \>) .
      
      assert (D[ f ] x > 0).
      {
        assert (a <= x <= b)
          by auto using Rlt_le, (\<< D[ f ] _ > 0 \>>) .
        auto using (\<< D[ f ] _ > 0 \>>) , (\< _ <= x <= _ \>) .
      }

      assert (b - a > 0)
        by auto using Rgt_minus, (\< a < b \>) .

      auto using Rmult_gt_0_compat, 
                 (\< D[ f ] x > 0 \>) , 
                 (\< b - a > 0 \>) .
    }

    apply Rminus_gt; auto using (\< f b - f a > 0 \>) .
  Qed.

End Spivak.

(* Local Variables: *)
(* company-coq-local-symbols: (("(\\<" . ?⟨) ("\\>)" . ?⟩) ("(\\<<" . ?≪) ("\\>>)" . ?≫)) *)
(* End: *)