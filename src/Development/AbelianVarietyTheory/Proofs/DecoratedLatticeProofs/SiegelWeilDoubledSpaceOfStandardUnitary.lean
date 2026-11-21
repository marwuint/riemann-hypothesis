import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sw_doubled_of_std : GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelWeilUnitaryConvergent := by
  intro hP D ψ A B hAB hB2 hW χB omh hWe a hMaj _ θ sS sB hθ hsS hsB hK mW 𝓨 hcov ν hν f hf
  obtain ⟨m0, hm0, hp0⟩ := _root_.GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.StdUnn.chart_exists D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hMaj κ hκ
  obtain ⟨lam, hlam, hψ', l, hl, hlabs⟩ := _root_.GlobalTheory.StdUnn.shift_char_realPar D ψ hWe.std θ hθ m0 hm0
  obtain ⟨omS, hT⟩ := _root_.GlobalTheory.StdUnn.exists_transport_std D ψ A B χB omh hWe mW 𝓨 hcov θ hθ κ
  obtain ⟨s', hs'std, hs'⟩ := _root_.GlobalTheory.StdUnn.CartanMove.cartan_move_std D A m0 hm0 κ hκ a p hp θ hθ sS hsS hK
  have hf' : IsFockVec ψ θ (dblSp A) B s' sB (omh ((p : GA D (dblSp A))⁻¹, 1) f) :=
    _root_.GlobalTheory.FockMove.isFockVec_om D ψ (dblSp A) B 1 χB omh hWe θ hθ sS s' sB _ hs' f hf
  have hschw := _root_.GlobalTheory.SchSchwartzAll.schSchwartz D
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B mW 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f),
      ((hschw ψ hWe.std θ hθ A B mW 𝓨 hcov).1 _ hf'.1)⟩
  have hΦ : Φ.1 ∈ fockA θ B A.rank l sB :=
    _root_.GlobalTheory.StdUnn.sch_mem_fockA D ψ hWe.std θ hθ A B mW 𝓨 hcov m0 hm0 s' sB hs'std hsB l hlabs _ hf'
  have hχ := _root_.GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χB B.rank hWe.hecT hWe.resT
  have hWS : IsWeilSch (shift ψ lam) χB⁻¹ θ B mW omS :=
    ⟨_root_.GlobalTheory.StdUnn.transport_levi D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     _root_.GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     _root_.GlobalTheory.StdUnn.WeylStd.main D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam⟩
  have hH := _root_.GlobalTheory.StdUnn.isHeight_hgtStd D A m0 hm0 κ hκ a p hp
  obtain ⟨hInt, hEis, hHol⟩ := hP D A.rank B hAB hB2 hW (shift ψ lam) hψ' χB⁻¹ hχ.1 hχ.2 θ hθ mW 𝓨 hcov omS hWS
    (hgtStd A a κ p) hH l hl sB hsB ν hν Φ hΦ
  obtain ⟨h0, hflat, hact⟩ := _root_.GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam a p f hf.1 Φ rfl
  have hth : ∀ g : GA D (dblSp A), theta omS Φ (κ (g * p)) = fun h => thetaKO omh g h f := fun g => by
    funext h
    rw [_root_.GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χB omh hWe mW 𝓨 hcov f hf.1 g h, theta, hact g]
  have hmean : ∀ g : GA D (dblSp A), GlobalTheory.ThetaMean.thetaMean omh ν f g = thetaInt omS ν Φ (κ (g * p)) := fun g => by
    rw [thetaInt, hth g]; rfl
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A m0 hm0 κ hκ
  have hG' := _root_.GlobalTheory.StdUnn.chart_mem_GF_iff D A m0 hm0 κ hκ
  have Heisenberg₂ := fun (z : ℂ) (hz : (A.rank : ℝ) / 2 < z.re) =>
    _root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG'
      (sect omS (hgtStd A a κ p) Φ z) (p : GA D (dblSp A)) (npow (absA D (aP A p)) (sZero A B - z))
      (flat A a (swSec A B omh mW 𝓨 f) (sZero A B) z) (fun g => hflat z g) (hEis z hz).1
  refine ⟨fun g => ?_, ⟨fun z hz => ⟨(Heisenberg₂ z hz).1, fun g => ((Heisenberg₂ z hz).2 g).1 ((hEis z hz).2 _)⟩, fun g => ?_⟩⟩
  · rw [← hth g]; exact hInt _
  · have hr : 0 < absA D (aP A p) := hom_pos _ _
    have := _root_.GlobalTheory.StdUnn.holValueAt_npow_sub_mul (fun z => GlobalTheory.Eis.cosetSum (P D A.rank) (GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) (κ (g * p)))
      (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh mW 𝓨 f) (sZero A B)) g) (s0 B A.rank) _ (absA D (aP A p))
      ((A.rank : ℝ) / 2) hr (hHol (κ (g * p))) (fun z hz => by
        rw [h0]; exact ((Heisenberg₂ z hz).2 g).2)
    rw [h0] at this
    rw [hmean g]
    exact this

end GlobalTheory.StdUnn
