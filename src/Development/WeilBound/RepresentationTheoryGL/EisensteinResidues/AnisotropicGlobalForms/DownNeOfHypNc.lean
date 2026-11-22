import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelSectionLeviMulEqAbsDetPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodinger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelSmoothInGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.ZetaEqIntegralIntegrandNc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralEisensteinResidue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Top

variable {D : D7}

theorem fockVec_of_vac_nc {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A H : HSp D} {sA : RealMat A} {sH : RealMat H}
    {f : WO A H → ℂ} (hf : IsThetaFunO ψ A H f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) : IsFockVec ψ θ A H sA sH f := by
  refine ⟨hf, 1, fun l hl => ?_⟩
  match l, hl with
  | [p], _ => exact hv p.1 p.2

theorem sphFun_of_param_nc {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

end GlobalTheory.Core.Rk.Exh.Top

end
