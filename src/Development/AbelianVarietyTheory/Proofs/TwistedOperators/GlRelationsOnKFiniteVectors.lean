import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

def kRes (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) :
    Module.End ℂ (kFinVec ε ρ) :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

end KPart

end GlobalTheory.GKLie
