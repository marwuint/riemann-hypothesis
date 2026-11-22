import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

variable (ρ : ∀ i, V i →+ E i)

variable [∀ i, FiniteDimensional ℝ (E i)]

end

end Formalism.HN

namespace Formalism.HN

end Formalism.HN
