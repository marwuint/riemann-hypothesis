import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteChainFrameBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistence

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BotFac

open GlobalTheory.SquareComm in
theorem finRel_le_ker {D : D7} {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)} {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : (WO M X → ℂ) →ₗ[ℂ] Pi) (h : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ) : finRel ω S ≤ LinearMap.ker p := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
  simp [map_sub, h u hu Ψ hΨ]

theorem tmul_ne_zero' {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (c : ℂ) (f : WO S T → ℂ) : thetaKO om g h (c • f) = c * thetaKO om g h f := by
  simp [thetaKO, map_smul]

theorem thetaKO_sub {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f - f') = thetaKO om g h f - thetaKO om g h f' := by
  simp [thetaKO, map_sub]

theorem thetaKO_add {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f + f') = thetaKO om g h f + thetaKO om g h f' := by
  simp [thetaKO, map_add]

theorem thetaKO_zero {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) :
    thetaKO om g h 0 = 0 := by
  simp [thetaKO]

end GlobalTheory.BotFac

end
