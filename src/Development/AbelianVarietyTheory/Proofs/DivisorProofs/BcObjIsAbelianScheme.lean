import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRhamCpl

open GlobalTheory.PDiv (ModPow)

section BaseChange

variable {O O' B B' : Type} [CommRing O] [CommRing O'] [CommRing B] [CommRing B']

abbrev bcObj (a : O →+* B) (A : Over (Sp O)) : Over (Sp B) := (Over.pullback (spMap a)).obj A

instance bcObj.instGrpObj (a : O →+* B) (A : Over (Sp O)) [GrpObj A] : GrpObj (bcObj a A) :=
  Functor.grpObjObj

def bcHom {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'} (h : a'.comp σ = τ.comp a)
    {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    (bcObj a' A').left ⟶ (bcObj a A).left :=
  pullback.lift (pullback.fst _ _ ≫ φ) (pullback.snd _ _ ≫ spMap τ) (by
    rw [Category.assoc, hφ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← Cris.spMap_comp, ← Cris.spMap_comp, h])

@[simp] theorem bcHom_fst {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'}
    (h : a'.comp σ = τ.comp a) {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left}
    (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    bcHom h hφ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ := pullback.lift_fst _ _ _

@[simp] theorem bcHom_snd {σ : O →+* O'} {a : O →+* B} {a' : O' →+* B'} {τ : B →+* B'}
    (h : a'.comp σ = τ.comp a) {A : Over (Sp O)} {A' : Over (Sp O')} {φ : A'.left ⟶ A.left}
    (hφ : φ ≫ A.hom = A'.hom ≫ spMap σ) :
    bcHom h hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap τ := pullback.lift_snd _ _ _

end BaseChange

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
    IsAbelianScheme A → (∃ g : ℕ, SmoothOfRelativeDimension g A.hom) →
    ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (E : Family p)

def Family.Natural : Prop :=
  ∀ ⦃R R' : Type⦄ [CommRing R] [CommRing R'] (hR : IsAdicComplete (Ideal.span {(p : R)}) R)
    (hR' : IsAdicComplete (Ideal.span {(p : R')}) R')
    ⦃A : Over (Sp R)⦄ [GrpObj A] ⦃A' : Over (Sp R')⦄ [GrpObj A']
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (hg : ∃ g : ℕ, SmoothOfRelativeDimension g A.hom) (hg' : ∃ g : ℕ, SmoothOfRelativeDimension g A'.hom)
    ⦃G : PDivGroup p R⦄ ⦃G' : PDivGroup p R'⦄ (t : G.TorsionTower A) (t' : G'.TorsionTower A')
    ⦃σ : R →+* R'⦄ ⦃φ : A'.left ⟶ A.left⦄
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A),
    E hR' hA' hg' t' (m.pull c) = (t'.semiHom t m).rig (E hR hA hg t c)

def Family.Filtered : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsAdicComplete (Ideal.span {(p : R)}) R) ⦃A : Over (Sp R)⦄
    [GrpObj A] (hA : IsAbelianScheme A) (hg : ∃ g : ℕ, SmoothOfRelativeDimension g A.hom)
    ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A),
    (PrimitiveSubmodule A).map (E hR hA hg t).toLinearMap = LinearMap.range G.rigOfOmega

def Family.Tangent : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsAdicComplete (Ideal.span {(p : R)}) R) ⦃A : Over (Sp R)⦄
    [GrpObj A] (hA : IsAbelianScheme A) (hg : ∃ g : ℕ, SmoothOfRelativeDimension g A.hom)
    ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (h : HdR A) (v : epsR R ⟶ A),
    IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie ((E hR hA hg t).symm.dualMap h)) v

end GlobalTheory.DeRhamCpl
