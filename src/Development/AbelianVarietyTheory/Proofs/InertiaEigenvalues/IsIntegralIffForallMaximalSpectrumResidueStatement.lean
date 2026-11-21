import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIffForallMaximalSpectrumResidue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ x : B.A, IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  exact @GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum
