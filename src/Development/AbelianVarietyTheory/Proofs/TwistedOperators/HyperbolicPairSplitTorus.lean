import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

theorem row_p {P : Matrix (Fin n) (Fin n) ℂ} {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (z : Fin n → ℂ) : ((Pᴴ * Jm ε * P) *ᵥ z) p = z q := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single q]
  · rw [hG p q (Or.inl rfl)]; simp
  · intro b _ hb; rw [hG p b (Or.inl rfl)]; simp [hb, hpq]
  · simp

theorem row_q {P : Matrix (Fin n) (Fin n) ℂ} {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (z : Fin n → ℂ) : ((Pᴴ * Jm ε * P) *ᵥ z) q = z p := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p]
  · rw [hG q p (Or.inr (Or.inl rfl))]; simp
  · intro b _ hb; rw [hG q b (Or.inr (Or.inl rfl))]; simp [hb, hpq.symm]
  · simp

theorem act {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (d : Fin n → ℂ) (hd : ∀ a, a ≠ p → a ≠ q → d a = 1) (y : Fin n → ℂ) :
    (P * diagonal d * P⁻¹) *ᵥ y = y + ((d p - 1) * bJ ε (P *ᵥ Pi.single q 1) y) • (P *ᵥ Pi.single p 1)
      + ((d q - 1) * bJ ε (P *ᵥ Pi.single p 1) y) • (P *ᵥ Pi.single q 1) := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  rw [coord hP q, coord hP p, row_q hpq hG, row_p hpq hG]
  have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, hPP, one_mulVec]
  have hdz : diagonal d *ᵥ (P⁻¹ *ᵥ y) = (P⁻¹ *ᵥ y) + ((d p - 1) * (P⁻¹ *ᵥ y) p) • Pi.single p 1
      + ((d q - 1) * (P⁻¹ *ᵥ y) q) • Pi.single q 1 := by
    funext a
    simp only [mulVec_diagonal, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hap : a = p
    · subst hap; simp [hpq]; ring
    · by_cases haq : a = q
      · subst haq; simp [hap]; ring
      · simp [hap, haq, hd a hap haq]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hdz, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hy]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

