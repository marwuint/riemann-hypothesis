import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.CollCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Core.Deg

theorem splits_level (D : D7) (w : D.what₂.Word) : SplitsE D (D.mem w).A.T :=
  S.splitsCompl_of_ncard _ _ (D.mem w).A.T_prime
    (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem w).A.T_prime (S.level_norm_one_mod_conductor _ w)).2

end GlobalTheory.CollCompare
