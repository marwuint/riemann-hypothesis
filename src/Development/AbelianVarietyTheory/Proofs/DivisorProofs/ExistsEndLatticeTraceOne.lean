import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

end GlobalTheory.LieDisc
