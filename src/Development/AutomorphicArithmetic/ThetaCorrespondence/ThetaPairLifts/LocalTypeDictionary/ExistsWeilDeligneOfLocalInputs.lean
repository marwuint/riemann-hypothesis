import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOverOfClauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyVertices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem exists_weilDeligne_of_localInputs (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : WeilEx := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS G => ?_⟩⟩
  obtain ⟨W, hW⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hP.weilRepresentationUnitaryPair R hS.core.lev
    hS.core.chain hS.core.models _ G
  haveI := hS.fin
  exact ⟨W, hW, GlobalTheory.FunObj.gridChoice_nonempty_of W hS.core.lev Set.finite_univ (GlobalTheory.RowClaim.Test.pde_ne_q hS)
    fun t _ P hP => GlobalTheory.RowClaim.Test.guard hS t P hP⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
