import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem isIntegrallyClosed_stalk_spec_field (K : Type) [Field K] (x : Spec (.of K)) :
    IsIntegrallyClosed ((Spec (.of K)).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec (.of K))
  letI := (Spec (.of K)).presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : (Spec (.of K)).Opens))
  have h1 := hU.isLocalization_stalk ⟨x, trivial⟩
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact (isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
    ((Spec (.of K)).presheaf.stalk x)).2

end GlobalTheory
