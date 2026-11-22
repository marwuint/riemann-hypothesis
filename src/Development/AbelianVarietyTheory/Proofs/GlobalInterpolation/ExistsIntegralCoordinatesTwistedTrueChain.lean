import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchin
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralHyperplaneFormOfLocalCoordsIntegra

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (I.rec7 l Z) (I.tw l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := _root_.GlobalTheory.PerQ.Co.coP_PtT_eq_blk I hI l Z l0 u a
           lat_co := _root_.GlobalTheory.PerQ.Co.latCo_mem_intSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨_root_.GlobalTheory.PtIntCoord.coP_mem_intSpan I hI l Z l0 u a w z hz, _root_.GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
