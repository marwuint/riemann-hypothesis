import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

def piSum_emb (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (i : ι) : E i →ₗ[ℝ] PiLp 2 E :=
  (WithLp.linearEquiv 2 ℝ (∀ j, E j)).symm.toLinearMap.comp (LinearMap.single ℝ E i)

theorem piSum_emb_apply (i : ι) (v : E i) (j : ι) : (piSum_emb E i v) j = Pi.single i v j := rfl

variable (ρ : ∀ i, V i →+ E i)

private theorem piReal_apply (ρ : ∀ i, V i →+ E i) (x : ∀ i, V i) (j : ι) :
    piReal ρ x j = ρ j (x j) := by
  rfl

variable [∀ i, FiniteDimensional ℝ (E i)]

end

end Formalism.HN

namespace Formalism.HN

end Formalism.HN
