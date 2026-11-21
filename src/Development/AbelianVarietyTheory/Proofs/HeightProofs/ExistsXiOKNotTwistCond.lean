import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Formalism.LocalRingCardinality.HostCls

noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin
open scoped TensorProduct

variable {D : D7}

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

end GlobalTheory.TwistFieldCompare
