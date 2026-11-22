import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageSmallNonzeroBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageKernelIntegrablePolynomialBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageThetaDictionaryExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageKer

theorem tmul_ne_zero_of_ne {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

end GlobalTheory.StageKer

end
