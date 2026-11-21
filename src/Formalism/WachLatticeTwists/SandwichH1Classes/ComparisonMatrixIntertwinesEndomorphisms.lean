import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

def Setup.eO {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) (a : R.Tt.Om) : R.OC :=
  R.emb (algebraMap R.Tt.Om R.Tt.Oi a)

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
