import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToForms
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChain
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerQ.lowerTieTwAt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  intro B X I hI l Z l0 u a
  exact ⟨(_root_.GlobalTheory.PerQ.ptT_forms_built I hI l Z l0 u a).1, (_root_.GlobalTheory.PerQ.ptT_forms_built I hI l Z l0 u a).2, _root_.GlobalTheory.PerQ.Co.pendTw_exists I hI l Z l0 u a⟩
