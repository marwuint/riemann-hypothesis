import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsMeasured
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Pf.Set3

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable (D : D7)

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

end Formalism.L2.SG.Pf.Set3
