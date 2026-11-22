import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittChangeBasisUnitaryIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupConjHermitianAutomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodinger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_eq_zero_of_comp {c : AF F} (hf : ∀ v, evFin F v c = 0) (hi : ∀ w, evInf F w c = 0) : c = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact Subtype.ext (funext fun v => hf v)

theorem tens_eq_zero_of_comp {z : AF F ⊗[F] E} (hf : ∀ v, compFin F E v z = 0) (hi : ∀ w, compInf F E w z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A),
      (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0 := by
    intro A _ _ f hz i
    have hs : z = ∑ j, B.repr z j • B j := (B.sum_repr z).symm
    have hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0 := by
      rw [hs] at hz
      simpa [B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Algebra.TensorProduct.map_tmul] using hz
    exact Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i
  have hc : ∀ i, B.repr z i = 0 := fun i =>
    adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)
  rw [← B.sum_repr z]
  simp [hc]

variable {σ : E →ₐ[F] E} {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
