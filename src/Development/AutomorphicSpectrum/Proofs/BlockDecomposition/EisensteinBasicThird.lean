import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open Ad3 Ad3.R
open GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact finAt_mul infAt_mul finAt_one infAt_one)
open GroundTheory.Automorphic.GLnLocal (integralGL)

namespace GlobalTheory.CompanionTheory.RSCompact

abbrev KV (v : Pl) : Type := integralGL (Qv v) 2

instance compactSpace_KV (v : Pl) : CompactSpace (KV v) :=
  isCompact_iff_compactSpace.1 (GLnLocal.isCompact_integralGL (Qv v) 2)

instance compactSpace_KA : CompactSpace KA :=
  isCompact_iff_compactSpace.1 Reduction.isCompact_maxCompact

instance secondCountable_KV (v : Pl) : SecondCountableTopology (KV v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end GlobalTheory.CompanionTheory.RSCompact

end
