import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrix

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := _root_.GlobalTheory.IntMatOpen.intMat_open_compact E w a b
  obtain ⟨hU', hc', hlc⟩ := _root_.GlobalTheory.LeviDesc.comp_linearAut_smooth_compact E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, _root_.GlobalTheory.HaarSum.hint_eq_integral _ μ hμ Λ hΛo hΛc _ hU' hc', _root_.GlobalTheory.HaarSum.hint_eq_integral _ μ hμ Λ hΛo hΛc _ hU hc,
    _root_.GlobalTheory.DetScale.integral_comp_matrix _ a b L hL φ μ hμ, _root_.GlobalTheory.ModAbs.haar_eq_absHalf_sq E w _ hL]
  ring
