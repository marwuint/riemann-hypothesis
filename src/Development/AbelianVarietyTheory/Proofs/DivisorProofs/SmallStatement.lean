import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

end GlobalTheory.ExpTie
