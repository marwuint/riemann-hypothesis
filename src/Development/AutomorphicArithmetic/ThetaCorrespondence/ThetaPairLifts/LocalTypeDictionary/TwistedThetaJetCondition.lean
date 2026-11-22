import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.TwistedThetaJetCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ
end
