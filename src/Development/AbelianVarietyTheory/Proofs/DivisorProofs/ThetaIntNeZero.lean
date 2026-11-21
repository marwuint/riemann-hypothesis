import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataDecomposesAtFinitePlaces

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
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

noncomputable section

namespace GlobalTheory.ConvThetaNe

open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Over

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem int_eq (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {ΦD : _} {Φ : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA ΦD Φ) (h : GA D X) : thetaInt ωA ν 𝓕 Φ h = Γ.M.I om ΦD (kapX X e hO.JX h) :=
  thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h

theorem integrable_big (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {Φ : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (h : GA D X) :
    IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := by
  obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
  have he := conjU_measurableEmbedding W 1 hO.JW
  have h1 := hC ΦD hD.1 (kapX X e hO.JX h)
  rw [hO.measW, hO.domW, he.integrableOn_map_iff, Set.preimage_image_eq _ he.injective] at h1
  have e1 : (fun g => thetaKO ωA g h Φ) = (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om ΦD g (kapX X e hO.JX h)) ∘
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW := funext fun g => (hO.theta_eq_A hD g h).symm
  rw [e1]
  exact h1

theorem exists_big_ne (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') :
    ∃ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ ≠ 0 := by
  obtain ⟨R, Rf, hm⟩ := hL _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1
  obtain ⟨f, hf, φ, hφ, hne⟩ := GlobalTheory.BigNZ.exists_I_ne_zero hm hc hco hla hl
  obtain ⟨Φ, hΦ, hD⟩ := hO.algA' _ (Submodule.subset_span ⟨f, φ, hf, hφ.fam.1, hφ.fam.2, rfl⟩)
  refine ⟨Φ, hΦ, fun h0 => hne (funext fun x => ?_)⟩
  obtain ⟨h, rfl⟩ := GlobalTheory.LineAtPlace.kapX_surj X e hO.JX x
  rw [← int_eq hO hD, h0]
  rfl

end Over

end GlobalTheory.ConvThetaNe

end
