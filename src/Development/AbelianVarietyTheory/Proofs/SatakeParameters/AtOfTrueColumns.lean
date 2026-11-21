import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrob
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTranslaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacobiOfClass
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PdvClose

theorem at_of_true_columns : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → t.Adapted → t.TopPinned → 3 ≤ B.host.splitBound → 5 ≤ K.dl1 → 4 ≤ K.dl2 → (∀ Ee : OrbitPlaces.Ent (I.rec7 l Z), OrbitPlaces.Shape (I.rec7 l Z) L Gi Ee ∧ ∀ u, ∀ j < B.R.m, ∀ s ∈ B.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * L.sc.a) → GlobalTheory.Pdv.At ex t.ent := by
  intro hAlg hG1 hCD hII B X I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC hAd hTop hsplit hdl1 hdl2 hSh
  have hDuty : GlobalTheory.Pdv.Duty t := _root_.GlobalTheory.Pdv.duty_of_std I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC
  have hHyp : t.Hyp := _root_.GlobalTheory.colSide_hyp _ L hT Gi Gl K Y cX ex t hDuty.col hTop
  have hInp : GlobalTheory.ThLoc.Inputs := GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates hAlg
  have hHost := GlobalTheory.KerStd.HostInert.hostAt_inert hG1 hCD hII
  obtain ⟨P, Bf, hK, he⟩ := hEntC
  obtain ⟨t', hc', hf'⟩ := hDuty.forms
  obtain ⟨ep, be, hBe, h0⟩ := _root_.GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit
  refine ⟨⟨_root_.GlobalTheory.Pdv.unUnit_stdKer I hOk hPins l Z L hT Gi Gl K Y cX ex t hStd,
    GlobalTheory.PdvKm.kmapRat_kerEntC' t P Bf hK he hDuty.rk,
    _root_.GlobalTheory.KFiClose.kFi_of_tie _ L hT Gi Gl K Y cX ex t' hc' hf',
    _root_.GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns I hOk hPins l Z ex.lev⟩, ep, be, (fun _ _ => -1), h0,
    _root_.GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit ep be _, ?_,
    _root_.GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d hInp _ L hT Gi Gl K Y cX ex t hHyp hsplit ep be _,
    _root_.GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted hInp _ L hT Gi Gl K Y cX ex t hHyp hAd ep be _,
    (hSh _).1⟩
  exact _root_.GlobalTheory.OrbitBoundStdRec.orbit_bound_rec _ L Gi K _ (hSh _).1 (hSh _).2 hdl1 hdl2 hBe rfl

end GlobalTheory.PdvClose
