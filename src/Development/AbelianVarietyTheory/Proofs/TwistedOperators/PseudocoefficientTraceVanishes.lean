import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

open GlobalTheory.HCChar GlobalTheory.Orb GlobalTheory.FlagLeviGroup

namespace GlobalTheory.IndTraceZero

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : GlobalTheory.RealInd.Flag n a}

theorem IsSplit.commute (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t g : UJ ε} (ht : IsSplit ε W x t)
    (hg : g ∈ flagM ε W) : g * t = t * g := by
  have hgi : g⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hg
  have hgg : uMat g * uMat g⁻¹ = 1 := by
    rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]; rfl
  have hJ : Jm ε * uMat g⁻¹ = (uMat g)ᴴ * Jm ε := by
    have := conjTranspose_inv_mul_Jm (ε := ε) g⁻¹
    rw [inv_inv] at this
    exact this.symm
  have hm : uMat (g * t * g⁻¹) = uMat g * uMat t * uMat g⁻¹ := rfl
  have h' : IsSplit ε W x (g * t * g⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hg ht.1) hgi, fun i y hy => ?_, fun y hy => ?_⟩
    · have hy' : uMat g⁻¹ *ᵥ y ∈ W i.succ := (hgi _ y hy).1
      have h1 := (hg _ _ (ht.2.1 i _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - (Real.exp (x i) : ℂ) • (uMat g⁻¹ *ᵥ y)) =
          uMat (g * t * g⁻¹) *ᵥ y - (Real.exp (x i) : ℂ) • y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hgg, Matrix.one_mulVec, hm]
      rwa [e] at h1
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat g⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hy _ (hg _ z hz).1
      have h1 := (hg _ _ (ht.2.2 _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - uMat g⁻¹ *ᵥ y) = uMat (g * t * g⁻¹) *ᵥ y - y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg,
          Matrix.one_mulVec, hm]
      rwa [e] at h1
  have e := (existsUnique_isSplit hW x).unique h' ht
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [e]

end GlobalTheory.IndTraceZero

namespace GlobalTheory.IndTraceZero

end GlobalTheory.IndTraceZero
