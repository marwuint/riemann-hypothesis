import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TQCompare
open GlobalTheory.UU

section Clauses
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem isGrpPullback_id_iff {B B' : Over S} [GrpObj B] [GrpObj B'] (β : B.left ⟶ B'.left) :
    IsGrpPullback B B' (𝟙 S) β ↔ ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom.left = β := by
  constructor
  · rintro ⟨hpb, hmul⟩
    have : IsIso β := hpb.isIso_fst_of_isIso
    have hw : β ≫ B'.hom = B.hom := by simpa using hpb.w
    obtain ⟨e, he⟩ : ∃ e : B ≅ B', e.hom.left = β := ⟨Over.isoMk (asIso β) hw, rfl⟩
    have key : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      intro T x y
      have h1 := hmul T x y (Over.homMk (x.left ≫ β) (by simp [hw])) (Over.homMk (y.left ≫ β) (by simp [hw]))
        rfl rfl
      apply Over.OverMorphism.ext
      simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Over.homMk_left, Category.assoc, he] at h1 ⊢
      exact h1.symm
    have hone : ∀ {M : Over S} [GrpObj M], (1 : 𝟙_ (Over S) ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    refine ⟨e, ⟨?_, ?_⟩, he⟩
    · have h2 := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h2
      have h3 : (1 : 𝟙_ (Over S) ⟶ B) ≫ e.hom = 1 := _root_.mul_left_cancel (h2.symm.trans (_root_.mul_one _).symm)
      rw [hone, hone] at h3
      exact h3
    · have h3 := key _ (fst B B) (snd B B)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h3
      rw [h3]
      congr 1
  · rintro ⟨e, he, rfl⟩
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
    intro T x y x₀ y₀ hx hy
    have hm := (IsMonHom.monoidHom e.hom T).map_mul x y
    simp only [IsMonHom.monoidHom_apply] at hm
    have h4 := congrArg Over.Hom.left hm
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Category.assoc] at h4 ⊢
    simp only [hx, hy]
    exact h4.symm

end Clauses

end GlobalTheory.TQCompare
end
