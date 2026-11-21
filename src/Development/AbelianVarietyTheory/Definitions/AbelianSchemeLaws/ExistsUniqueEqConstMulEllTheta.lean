import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsGrpObjIsAddLawHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SymmetricLineBundleOfRegularSection
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)

variable [W.IsElliptic]

theorem appLE_originSec_eq_zero_iff_eSec (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left)
    (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
      t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := by
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact appLE_originSec_eq_zero_iff W t i h

theorem rigidified_originLB : Out.Rigidified (schemeOver W) (originLB W) := by
  unfold Out.Rigidified
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact ⟨_, isGen_one_pull_zero W⟩

theorem sym_originLB : Out.Sym (schemeOver W) (originLB W) := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  have : IsIso (GrpObj.inv : schemeOver W ⟶ schemeOver W).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : schemeOver W ⟶ schemeOver W)))
  have hreg := fun i V h => ((isRegularSec_originSec W i).resG (V := V) h).mem
  refine SameZeroScheme.exists_isGen_linComb (schemeOver W).left _ (originLB W) (originSec W) _ _
    (originLB_isLB W)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [appLE_originSec_eq_zero_iff_eSec, appLE_originSec_eq_zero_iff_eSec, ← Category.assoc t]
  exact SymOfZeroDivisor.inv_eq_zero_iff (schemeOver W) _

theorem kTriv_originLB : Out.KTriv (schemeOver W) (originLB W) := by
  refine kTriv_of_sections_vanish_on_zero _ (schemeOver W) (originLB W) (originSec W)
    (originLB_isLB W) (appLE_originSec_eq_zero_iff_eSec W) ?_
  intro R' _ f Y φ q H s T t j h e
  rw [show eSec (schemeOver W) = zero W from one_left W] at e
  exact appLE_sec_pull_originLB_eq_zero W H s t j h e

def ellPolAV : Out.PolAV (Spec (CommRingCat.of R)) where
  A := schemeOver W
  grp := grpObj W
  isAb := isAbelianScheme_schemeOver R W W.isUnit_Δ (isCommMonObj W)
  g := 1
  smoothDim := smoothOfRelativeDimension_toSpec_of_isUnit W W.isUnit_Δ
  L := originLB W
  isLB := originLB_isLB W
  rigid := rigidified_originLB W
  sym := sym_originLB W
  ample := relAmple_originLB W
  ktriv := kTriv_originLB W

theorem ellPolAV_A : (ellPolAV W).A = schemeOver W := rfl

theorem ellPolAV_hom : (ellPolAV W).A.hom = toSpec W := rfl

theorem ellPolAV_grp : (ellPolAV W).grp = grpObj W := rfl

@[simp] theorem ellPolAV_g : (ellPolAV W).g = 1 := rfl

theorem ellPolAV_L : (ellPolAV W).L = originLB W := rfl

theorem eSec_ellPolAV : eSec (ellPolAV W).A = zero W := one_left W

def ellTheta : (ellPolAV W).L.Sec := originSec W

theorem ellTheta_eq : ellTheta W = originSec W := rfl

theorem exists_isLieBasis_ellPolAV : ∃ v : epsR R ⟶ (ellPolAV W).A,
    (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
      v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
    IsLieBasis ![v] :=
  WeierstrassLie.isLieBasis_eps R W (one_left W)

end GlobalTheory.WeierstrassCurve
