import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardBaseLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompari
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardBaseLevelPoints
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.duty_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t hN hJ htw hS hE
  obtain ⟨t', hS', hR', -⟩ := _root_.GlobalTheory.Pdv.stdKer_stdRd I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  refine ⟨_root_.GlobalTheory.Pdv.colSide_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t hN hS, hE, _root_.GlobalTheory.Pdv.rk_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS,
    ⟨t', _root_.GlobalTheory.Pdv.colSide_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS', ?_⟩⟩
  intro u μ _
  refine ⟨GlobalTheory.Pdv.stabStd I l Z u μ, ?_, _root_.GlobalTheory.Pdv.stab_pin I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS' hR' u μ⟩
  rw [htw]
  exact _root_.GlobalTheory.Pdv.FormsStd.formsAre_stabStd I hOk hP l Z l0 Y.Qp t'.O hS'.O u μ
