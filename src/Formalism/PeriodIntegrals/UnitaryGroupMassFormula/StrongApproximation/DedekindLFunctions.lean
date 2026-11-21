import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall
import Lemmata.Cancellation.EnnrealVolumeRatioStepCancel

noncomputable section

open IsDedekindDomain NumberField

namespace PI.StrongApproxE

namespace DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem sa (T : Finset (HeightOneSpectrum R)) (a c : HeightOneSpectrum R → K) (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : K, (∀ p ∈ T, p.valuation K (t - a p) ≤ p.valuation K (c p)) ∧
      ∀ p, p ∉ T → p.valuation K t ≤ 1 := by
  first | exact Bl.VolumeRatioCancellation.goal1 .. | (apply Bl.VolumeRatioCancellation.goal1 <;> assumption) | (intros; apply Bl.VolumeRatioCancellation.goal1 <;> assumption)

end DedekindLFunctions

theorem strong_approximation_finite_places : DedSA := by
  intro F _ _ T a c hc
  exact DedekindLFunctions.sa (R := 𝓞 F) (K := F) T a c hc

end PI.StrongApproxE
