import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIdx

def swapAlg (k : Type) [CommRing k] : (k × k) ≃ₐ[k] k × k :=
  { (RingEquiv.prodComm : k × k ≃+* k × k) with commutes' := fun _ => rfl }

end GlobalTheory.CompanionTheory.SplitIdx
