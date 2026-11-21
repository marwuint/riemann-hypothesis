import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVectorStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransferStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem heckeFormAniso_of_global_euler (D : D7) (hG : GlobalFormAniso D) (hE : EulerRight D) : HeckeFormAniso D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := GlobalTheory.T.flatFamilyZeta_convergence_holomorphy (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := _root_.GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

theorem rcoef_one {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    rcoef m (fun _ : GA D A => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend, volQ]

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

theorem prod_range_sub_eq_prod_Icc (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

end GlobalTheory.BottomRallis
