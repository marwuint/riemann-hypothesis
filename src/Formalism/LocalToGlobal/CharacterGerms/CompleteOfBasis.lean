import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl
import Lemmata.MiscLemmasH.Imports

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Lift

variable {A : Type} [CommRing A] (I : Ideal A)

theorem lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)

theorem idem_zero [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _

end Lift

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
