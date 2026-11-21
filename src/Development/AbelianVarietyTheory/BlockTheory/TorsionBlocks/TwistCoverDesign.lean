import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev ModHost (D : D7) : Type := ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro hz
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [FractionalIdeal.coeIdeal_eq_zero] at h1
    unfold Formalism.BasicNotions.Host.ccE at h1
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact D.host.ccK_ne_bot h1
  · rw [inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h1
    have h2 := D.host.𝔟_spec.2
    rw [h1] at h2
    simp at h2

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
