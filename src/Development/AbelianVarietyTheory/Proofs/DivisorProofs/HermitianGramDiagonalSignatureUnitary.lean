import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCovolConj
open MeasureTheory Set
open scoped Pointwise

section General

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

end General
section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G M).det = M.det * (G.map τ).det * starRingEnd ℂ M.det := by
  rw [gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]

theorem col_eq_mulVec (M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col M a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (1 : Matrix (Fin r) (Fin r) ℂ) a := by
  ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]

end Concrete

end GlobalTheory.SUCovolConj
end
