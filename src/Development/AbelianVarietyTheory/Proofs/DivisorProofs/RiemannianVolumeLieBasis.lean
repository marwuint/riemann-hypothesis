import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap

noncomputable section

namespace GlobalTheory.SUVol.LieMeas

open MeasureTheory Matrix
open scoped ENNReal

section Main

open NumberField GlobalTheory.SUVol GlobalTheory.SUVol.DensOne ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def toFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) where
  toFun X := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X p.1) * mat x p.1) p.2.1 p.2.2)
  map_add' X Y := by
    refine PiLp.ext fun p => ?_
    have e : Matrix.of ((X + Y) p.1) = Matrix.of (X p.1) + Matrix.of (Y p.1) := rfl
    simp only [PiLp.add_apply, e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c X := by
    refine PiLp.ext fun p => ?_
    have e : Matrix.of ((c • X) p.1) = c • Matrix.of (X p.1) := rfl
    simp only [PiLp.smul_apply, e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

end Main

end GlobalTheory.SUVol.LieMeas
