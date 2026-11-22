import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerDecTwTOfStd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPair
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainData
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem twistedPeriodAdmissible_of_rowInt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → ∀ Y : DivX (I.rec7 l Z), Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (I.rec7 l Z) Y (I.tw l l0 Z) := by
  intro B X I hOk hPins l Z l0 hRow nch tp hxi Y
  obtain ⟨C, hC, hLv⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hOk hPins l Z
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std I hOk hPins l Z l0 nch tp C hxi hC hLv
  have hT := GlobalTheory.PerTwClose.perDecTwT_of_std I hOk l Z l0 hRow (I.cf l Z) nch tp C t Y ht
  refine _root_.GlobalTheory.PerRedU.main (I.rec7 l Z) Y (I.tw l l0 Z) ?_
  intro u μ hμ _
  exact _root_.GlobalTheory.PerRedTw.reduction_perDecTw (I.rec7 l Z) (I.cf l Z) nch tp C (I.tw l l0 Z) t Y u μ hμ (hT u μ hμ)

end GlobalTheory.PerTwClose
