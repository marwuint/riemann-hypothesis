import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Formalism.HermitianLattices.StatementMass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    _root_.GlobalTheory.Mass.siegelMassRatio_holds D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
