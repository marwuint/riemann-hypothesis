import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsLatticeOfCompactOpen
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.IdxAd

def swapC (k : Type) [CommRing k] : (k × k) →ₐ[k] k × k := (GlobalTheory.CompanionTheory.SplitIdx.swapAlg k).toAlgHom

theorem swapC_apply {k : Type} [CommRing k] (z : k × k) : swapC k z = z.swap := rfl

end GlobalTheory.CompanionTheory.IdxAd
