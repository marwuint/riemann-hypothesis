import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.FieldOfDefinitionDescentProp : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕
end
