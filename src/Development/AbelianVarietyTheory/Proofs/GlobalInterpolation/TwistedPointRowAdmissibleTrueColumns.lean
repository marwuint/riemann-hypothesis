import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumns
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LowerTwistedCompatibleOfEvaluationBranching
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem twistedPointIntegral_of_TC_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  intro B X I hI l Z l0 u μ _ _
  exact Formalism.MainNotions.DIV.HookProducts.AdmPtTw.lowerTieTwAt_integral
    (_root_.GlobalTheory.PerQ.lowerTieTwAt_to_lib _ _ u μ (_root_.GlobalTheory.PerQ.lowerTieTwAt_all I hI l Z l0 u μ))

end GlobalTheory.PerQ
