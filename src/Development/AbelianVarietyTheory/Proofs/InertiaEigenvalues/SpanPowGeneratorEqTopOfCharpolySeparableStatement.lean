import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  exact @GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable
