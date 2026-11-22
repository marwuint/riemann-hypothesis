import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end GlobalTheory.LieDisc
