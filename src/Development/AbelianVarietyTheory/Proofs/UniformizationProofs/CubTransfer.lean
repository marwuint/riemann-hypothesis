import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GoodReductionUnif

theorem exists_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (A : PolAV S') (eA : (Over.pullback f).obj P.A ≅ A.A), IsMonHom eA.hom ∧
      ∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom f)), w.IsGen := by
  obtain ⟨A, g, hg, -, mul, t, ht⟩ := hB S S' f P
  let eA : (Over.pullback f).obj P.A ≅ A.A := Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd
  have he : eA.hom.left ≫ g = pullback.fst P.A.hom f := hg.isoPullback_inv_fst
  refine ⟨A, eA, isMonHom_of_mul _ fun T x y => Over.OverMorphism.ext (hg.hom_ext ?_ ?_), ?_⟩
  · have tb : ∀ a : T ⟶ (Over.pullback f).obj P.A, toBase hg.w (a ≫ eA.hom) =
        toBase (A := P.A) (A' := (Over.pullback f).obj P.A) (g := pullback.fst P.A.hom f) pullback.condition a :=
      fun a => Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) he))
    have e : toBase hg.w ((x * y) ≫ eA.hom) = toBase hg.w ((x ≫ eA.hom) * (y ≫ eA.hom)) := by
      rw [mul, tb, tb, tb, toBase_mul_pullback]
    exact congrArg CommaMorphism.left e
  · exact (Over.w _).trans (Over.w _).symm
  · obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
    have h₁ := (isGen_iff t').1 ht'
    have h₂ := (isGen_iff _).1 (pullIso_isGen A.isLB eA.hom.left)
    obtain ⟨w, Tw⟩ := Geo.Tor.exists_comp A.isLB t' (pullIso A.L eA.hom.left) h₁ h₂ P.isLB
      (pull_isLB A.isLB _)
    rw [← he]
    exact ⟨w, (isGen_iff w).2 (Tw.pgen_comp A.isLB h₁ h₂)⟩

end GlobalTheory.GoodReductionUnif

end
