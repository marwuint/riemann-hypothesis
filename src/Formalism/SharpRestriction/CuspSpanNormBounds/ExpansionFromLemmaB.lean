import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem integral_normSq_coef {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} :
    ∫ g, f g * star (f g) ∂μ = ((∫ g, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem inner_self_C {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  simp

theorem fdegOf_eq {μ : Measure (Formalism.REAL.UJ ε)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg μ σ d) {v : H} (hv : v ≠ 0) : fdegOf μ σ v = d := by
  obtain ⟨hd, hF⟩ := h
  have e := (hF v v v v).2
  rw [integral_normSq_coef, inner_self_C] at e
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e' : (∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ) = ‖v‖ ^ 4 / d := by
    have : (((∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ : ℝ)) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [e]; push_cast; ring_nf
    exact_mod_cast this
  unfold fdegOf
  rw [e']
  field_simp

end Fdeg

section P90P

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem ds_one (hσ : IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h := hDS.2.2.1.1.1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  simpa [Matrix.nonsing_inv_mul _ hu] using h

theorem ds_inv_adj (hσ : IsDSHpk k r ε lam σ) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (y z : H) : ⟪σ a⁻¹ y, z⟫_ℂ = ⟪y, σ a z⟫_ℂ := by
  have h1 := Formalism.MainNotions.LeviCoordinates.discrete_series_inner hσ ha (σ a⁻¹ y) z
  have h2 : σ a (σ a⁻¹ y) = y := by
    have e : σ (a * a⁻¹) = (σ a).comp (σ a⁻¹) := Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha (uh_inv ha)
    rw [Matrix.mul_nonsing_inv _ (isUnit_of_uh ha), ds_one hσ] at e
    have := congrArg (fun T : H →L[ℂ] H => T y) e
    simpa using this.symm
  rw [h2] at h1
  exact h1.symm

end P90P

section Named

open Formalism.QuantumDeterminants.WeylGroupFacts

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end Named

end Formalism.MainNotions.DiscreteSeriesInnerProducts
