import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

end GlobalTheory.FinPartAt
