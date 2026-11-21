import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

namespace Line

def lineMetricScaled (c : ℝ) (hc : 0 < c) : HermMetric yLine (trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart where
  m := 2
  chart l := fun _ => l
  fr _ := 1
  b _ := Pi.basisFun Ω (Fin 2)
  isFrame l := lineMetric.isFrame l
  gram _ _ := (c : ℂ) • 1
  cover := lineMetric.cover
  posDef _ _ _ _ := Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hc)
  compat l l' z hz hl hl' S hS Sz hSz := by
    have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) = Szᴴ * 1 * Sz :=
      lineMetric.compat l l' z hz hl hl' S hS Sz hSz
    show (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = Szᴴ * ((c : ℂ) • 1) * Sz
    rw [Matrix.mul_smul, Matrix.smul_mul, ← h]
  torus _ _ _ _ _ _ := rfl
  conj _ _ _ _ := by
    ext p q
    by_cases h : p = q <;> simp [h]
  smooth _ _ _ _ _ _ _ _ := contDiffAt_const
  logBound a t₀ _ := by
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hinv : ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ = (c : ℂ)⁻¹ • 1 := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    refine ⟨a, inFrameDomain_line (by rw [lineChart_γ, chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, c⁻¹, inv_pos.mpr hc, c⁻¹, inv_pos.mpr hc, fun t _ _ _ _ => ⟨?_, ?_, ?_⟩⟩
    · show (((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ - ((c⁻¹ : ℝ) : ℂ) • 1).PosSemidef
      rw [hinv, Complex.ofReal_inv, sub_self]
      exact Matrix.PosSemidef.zero
    · show ((((c⁻¹ * (lineChart a).logR t : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹).PosSemidef
      rw [logR_lineChart, hinv]
      have : (((c⁻¹ * Real.exp 1 : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (c : ℂ)⁻¹ • 1 =
          ((c⁻¹ * (Real.exp 1 - 1) : ℝ) : ℂ) • 1 := by
        rw [← sub_smul]
        congr 1
        push_cast
        ring
      rw [this]
      refine Matrix.PosSemidef.one.smul ?_
      refine Complex.zero_le_real.mpr (mul_nonneg (inv_nonneg.mpr hc.le) ?_)
      exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    · intro p q
      show ‖fderiv ℝ (fun _ : Fin 1 → ℂ => ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) p q) t‖ ≤ _
      rw [fderiv_const_apply, norm_zero]
      positivity

def lineDataScaled (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) : ComponentData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  { lineData II hII with h := fun _ => lineMetricScaled c hc }

theorem lineDataScaled_f (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).f = 1 := rfl

theorem lineDataScaled_N (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).N = 2 := rfl

theorem lineDataScaled_j' (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).j' = 1 := rfl

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
