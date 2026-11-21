import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodAdelicClausesOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominates
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLattices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodValueLipschitzRealOneParameter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMultiplicityValueExceedsHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.PerNe

theorem multT_apply_mul_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {F : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    ∀ k ∈ J, ∀ g, F v (g * k) = χ k * F v g := by
  obtain ⟨T, hT, rfl⟩ := hF
  induction hT using Submodule.span_induction generalizing v with
  | mem T hT =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      intro k hk g
      simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
      rw [hT.lev w k hk g]; ring
    | add x y hx hy =>
      intro k hk g
      simp only [map_add, Pi.add_apply]
      rw [hx k hk g, hy k hk g]; ring
  | zero => intro k hk g; simp
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro k hk g
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [h₁ v k hk g, h₂ v k hk g]; ring
  | smul c T _ h =>
    intro k hk g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [h v k hk g]; ring

theorem apply_tprod_eq {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (y : (⨂[ℂ] i, E i) →ₗ[ℂ] X) (a : ∀ i, E i) :
    y (PiTensorProduct.tprod ℂ a) = PiTensorProduct.lift.symm y a := by
  conv_lhs => rw [← PiTensorProduct.lift.apply_symm_apply y]
  exact PiTensorProduct.lift.tprod _

end GlobalTheory.SepPer.PerNe

namespace GlobalTheory.SepPer

end GlobalTheory.SepPer

end
