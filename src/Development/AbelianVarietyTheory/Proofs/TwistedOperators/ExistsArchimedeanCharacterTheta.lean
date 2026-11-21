import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Kronecker Matrix

namespace GlobalTheory.BottomRealChar

open GlobalTheory.Grid (neg sgn ofSgn)

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

theorem commGroup_div_eq_div_mul_ratio {G : Type*} [CommGroup G] (a x y e c : G) :
    c * e / (a * x * e) = c * e / (a * y * e) * (y * x⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

def detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) : GinfC V →* ℂ where
  toFun g := ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ
  map_one' := by
    simp only [OneMemClass.coe_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, Finset.prod_const_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]

theorem detChar_apply {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V) :
    detChar θ V e g = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ := rfl

theorem continuous_detChar {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (e : D.what₂.Tau → ℤ) :
    Continuous (detChar θ V e) := by
  refine continuous_finset_prod _ fun τ _ => Continuous.zpow₀ ?_ _ fun g => Or.inl fun h0 => ?_
  · exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val))).matrix_det
  · have := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g.1)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

theorem isAlgebraic_detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V)
    (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)) : IsAlgebraic ℚ (detChar θ V e g) := by
  let K := algebraicClosure ℚ ℂ
  have hK : ∀ z : ℂ, z ∈ K ↔ IsAlgebraic ℚ z := fun z => mem_algebraicClosure_iff
  rw [← hK, detChar_apply]
  refine prod_mem fun τ _ => zpow_mem ?_ _
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => (hK _).2 (hg τ _ _))

end GlobalTheory.BottomRealChar

end
