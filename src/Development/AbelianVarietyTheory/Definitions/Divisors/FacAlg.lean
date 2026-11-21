import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

end GlobalTheory.Mum
