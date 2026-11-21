import Mathlib
import GroundTheory.TateCohomology.TateShapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

section Res

noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom

lemma tateRes_app (n : ℤ) (A : Rep.{u} k G) :
    (tateRes S n).app A =
      (tateCohomologyFunctor n).map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) ≫
        (tateCoindIso S (res S.subtype A) n).hom := by
  simp only [tateRes, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

@[simps]
noncomputable def resCoindUnitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    X ⟶ (X.map (resFunctor S.subtype)).map (coindFunctor k S.subtype) where
  τ₁ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₁
  τ₂ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₂
  τ₃ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₃
  comm₁₂ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.f).symm
  comm₂₃ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.g).symm

end Res

section Cores

open scoped Classical in

noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom

lemma tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by
  simp only [tateCores, NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

@[simps]
noncomputable def indResCounitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    (X.map (resFunctor S.subtype)).map (indFunctor k S.subtype) ⟶ X where
  τ₁ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₁
  τ₂ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₂
  τ₃ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₃
  comm₁₂ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.f).symm
  comm₂₃ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.g).symm

end Cores

end GroundTheory.GroupCoh
