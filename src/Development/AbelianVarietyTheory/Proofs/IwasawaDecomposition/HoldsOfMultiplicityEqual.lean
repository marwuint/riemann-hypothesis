import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowPartNeBotPositiveDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsLOfCopy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.LiftsAt

open GlobalTheory.Mem.Top.GroupRetwisting

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P W} (h : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) _ hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (h.ser k f).trans (_root_.GlobalTheory.SerCmp.eSerC_eq_eSerO hG _ _ _ _ _ (h.teich k) O hO D.R.r f hr)⟩

def Closes (X : Stages) : Prop :=
  ∀ (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Tw : TwDat X.B) (Wt : Set X.B.places.Pl) (z : Dat X I hX Tw Wt),
    TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → z.R.toRealDat.LIntegral →
      HoldsL z.R z.F

set_option maxHeartbeats 2000000 in

theorem ties_at (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (hN : GrpTrue Z.N f)
    (ok : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1) (hEx : z.R.toRealDat.ExAt)
    (host : Formalism.IndefR.Links.HostHyp (w.st Z).toD7) (par : ∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L))
    (hn : 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV)
    (hI : IoExt z.R.toRealDat) (hU : z.R.toRealDat.LUnif) (hW : CoverAt.WeberLev B f T) :
    TiesB z.R z.F ∧ TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have ty : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    have e : z.R.toLevCh.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg (Fr.at (w.st Z)) w.C_eq)
    have e' : z.R.C = Fr.at (w.st Z) f := e
    rw [e']
    exact hN
  have hch := z.pins.char
  refine ⟨⟨ok, hch, hEx, host, par, B.ccK_top, z.pins.keep.guard,
    GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev ty, serClause_of_typesTrue hG _ ty,
    GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, z.pins.trSem, z.pins.keep.std, z.pins.phs, hn⟩,
    TiesG.of_dat z hU hI (fun i => ?_) (CoverAt.coverField_of_weberLev hW w Z hX Wt z)⟩
  exact GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) hn hch hEx ⟨z.geo.fw⟩ hI i
    (z.geo.pins i) (z.geo.phase i hU)

end GlobalTheory.Mem.R3.LiftsAt

end
