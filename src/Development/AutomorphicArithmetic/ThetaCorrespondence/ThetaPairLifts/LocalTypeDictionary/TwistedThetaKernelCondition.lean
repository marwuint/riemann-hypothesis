import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.TwistedThetaKernelCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0
end
