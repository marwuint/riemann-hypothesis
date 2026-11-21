import Mathlib
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
