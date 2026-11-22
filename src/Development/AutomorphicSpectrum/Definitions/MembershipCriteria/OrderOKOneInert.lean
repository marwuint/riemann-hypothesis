import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

noncomputable section

open MeasureTheory Matrix GlobalTheory.WeilM ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.VacLoc

structure Inert (k : Type) [Field k] [ValuativeRel k] {E : Type} [CommRing E] [Algebra k E] (c : E →ₐ[k] E) (ξ : E) :
    Prop where
  quad : IsQuad c ξ
  two : valuation k (2 : k) = 1
  sq : ∃ δ : k, valuation k δ = 1 ∧ ξ * ξ = algebraMap k E δ ∧ ∀ y : k, valuation k y ≤ 1 → valuation k (y * y - δ) = 1

namespace Unr

end Unr

end GlobalTheory.CompanionTheory.VacLoc
