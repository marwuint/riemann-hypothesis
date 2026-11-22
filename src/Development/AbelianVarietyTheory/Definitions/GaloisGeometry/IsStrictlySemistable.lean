import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSSFun
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableModel

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.LogCris

variable {O : Type} [CommRing O]

def ptFun (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k) :
    CommRingCat.{0} ⥤ Type where
  obj B := PtOver X q κ B
  map {B B'} φ := TypeCat.ofHom fun z => ⟨(φ.hom.comp z.1.1, Spec.map φ ≫ z.1.2), by
    rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩
  map_id B := by
    ext z
    · rfl
    · change Spec.map (𝟙 B) ≫ z.1.2 = z.1.2
      rw [Spec.map_id, Category.id_comp]
  map_comp f g := by
    ext z
    · rfl
    · simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_res {B : Type} [CommRing B] {X : Scheme.{0}}
    (y : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (hV : V ≤ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V) (a : Γ(X, U)) :
    _root_.GlobalTheory.Cris.evalAt y V h' (X.presheaf.map (homOfLE hV).op a) = _root_.GlobalTheory.Cris.evalAt y U h a := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in
private theorem gammaSpecIso_hom_appLE_spec_map {A C : CommRingCat.{0}} (χ : A ⟶ C)
    (e : (⊤ : (Spec C).Opens) ≤ Spec.map χ ⁻¹ᵁ ⊤) (b : Γ(Spec A, ⊤)) :
    (Scheme.ΓSpecIso C).hom ((Spec.map χ).appLE ⊤ ⊤ e b) = χ ((Scheme.ΓSpecIso A).hom b) := by
  have h1 : (Spec.map χ).appLE ⊤ ⊤ e = (Spec.map χ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h1, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_map {B B' : CommRingCat.{0}} {X : Scheme.{0}} (φ : B ⟶ B')
    (y : Spec B ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U) (a : Γ(X, U)) :
    _root_.GlobalTheory.Cris.evalAt (B := B') (Spec.map φ ≫ y) U h' a =
      φ.hom (_root_.GlobalTheory.Cris.evalAt (B := B) y U h a) := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) y U ⊤ ⊤ h le_top, CommRingCat.comp_apply]
  exact gammaSpecIso_hom_appLE_spec_map φ _ _

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_base {B : Type} [CommRing B] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k]
    (κ : O →+* k) (ψ : k →+* B) (y : Spec (CommRingCat.of B) ⟶ X)
    (hy : y ≫ q = Spec.map (CommRingCat.ofHom (ψ.comp κ))) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U) (a : O) :
    _root_.GlobalTheory.Cris.evalAt y U h ((q.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) =
      ψ (κ a) := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (q.appLE ⊤ U le_top) (y.appLE U ⊤ h),
    Scheme.Hom.appLE_comp_appLE y q ⊤ U ⊤ le_top h]
  have key : ∀ (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of O)),
      f = Spec.map (CommRingCat.ofHom (ψ.comp κ)) → ∀ e,
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom (f.appLE ⊤ ⊤ e ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) =
        ψ (κ a) := by
    rintro f rfl e
    rw [gammaSpecIso_hom_appLE_spec_map]
    simp
  exact key _ hy _

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.le_preimage_inf {B : Type} [CommRing B] {X : Scheme.{0}}
    (y : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) :=
  le_inf h h'

theorem le_preimage_map {B B' : CommRingCat.{0}} {X : Scheme.{0}} (φ : B ⟶ B') (y : Spec B ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U :=
  fun p _ => h (Set.mem_univ ((Spec.map φ) p))

structure SSAtlas (ϖ : O) (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) (ι A : Type) [Fintype ι] where

  U : A → X.Opens
  affine : ∀ α, IsAffineOpen (U α)
  cover : (⨆ α, U α) = ⊤

  F : ∀ α, ι → Γ(X, U α)

  G : ∀ α β, ι → Γ(X, U α ⊓ U β)ˣ
  prod_F : ∀ α, ∏ i, F α i = (q.appLE ⊤ (U α) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)
  F_eq : ∀ α β i, X.presheaf.map (homOfLE inf_le_left).op (F α i) =
      (G α β i : Γ(X, U α ⊓ U β)) * X.presheaf.map (homOfLE inf_le_right).op (F β i)
  nzd : ∀ α i, F α i ∈ nonZeroDivisors Γ(X, U α)
  chart : ∀ α (x : X), x ∈ U α → ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (hV : V ≤ U α) (m r : ℕ) (_ : 1 ≤ r)
      (_ : r ≤ m) (c : Fin r ↪ ι)
      (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < r),
        MvPolynomial.X j) - MvPolynomial.C ϖ}) →+* Γ(X, V)),
      ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ V le_top).hom ∧
      (∀ j : Fin r, ∃ u : Γ(X, V)ˣ, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castLE (by omega) j))) =
        u * X.presheaf.map (homOfLE hV).op (F α (c j))) ∧
      ∀ i, i ∉ Set.range c → IsUnit (X.presheaf.map (homOfLE hV).op (F α i))
  G_self : ∀ α i, G α α i = 1
  G_comp : ∀ α β γ i,
    X.presheaf.map (homOfLE (inf_le_left : U α ⊓ U β ⊓ U γ ≤ U α ⊓ U β)).op (G α β i : Γ(X, U α ⊓ U β)) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U α ⊓ U β ⊓ U γ ≤ U β ⊓ U γ)).op (G β γ i : Γ(X, U β ⊓ U γ)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U α ⊓ U β ⊓ U γ ≤ U α ⊓ U γ)).op (G α γ i : Γ(X, U α ⊓ U γ))
  prod_G : ∀ α β, ∏ i, G α β i = 1

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  (C : SSAtlas ϖ X q ι A) {k : Type} [CommRing k] (κ : O →+* k)

end SSAtlas

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  {k : Type} [CommRing k] (κ : O →+* k)

end SSAtlas

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  {k : Type} [CommRing k] (κ : O →+* k)

end SSAtlas

section Model

variable (ϖ : O)

set_option autoImplicit false in
variable {O : Type} [CommRing O] (ϖ : O) in

theorem _root_.GlobalTheory.LogCris.model_mul_eq_zero {m r : ℕ} (hϖ : ϖ ∈ nonZeroDivisors O)
    (g : _root_.GlobalTheory.Et.ssModel O ϖ m r)
    (h : algebraMap O _ ϖ * g = 0) : g = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  set S := Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)
  set d : Fin m →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1
  have hX : (∏ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin m) O) = MvPolynomial.monomial d 1 := by
    simp only [d, MvPolynomial.X, MvPolynomial.monomial_sum_one]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  have h2 : MvPolynomial.C ϖ * g ∈
      Ideal.span {(∏ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin m) O) - MvPolynomial.C ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact h
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.mp h2
  rw [hX] at hp
  have hc : ∀ s, ϖ ∣ MvPolynomial.coeff s p := by
    intro s
    have := congrArg (MvPolynomial.coeff (d + s)) hp
    rw [mul_sub, MvPolynomial.coeff_sub, mul_comm p (MvPolynomial.monomial d 1), mul_comm p (MvPolynomial.C ϖ),
      MvPolynomial.coeff_monomial_mul, one_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at this
    exact ⟨MvPolynomial.coeff (d + s) g + MvPolynomial.coeff (d + s) p, by rw [mul_add, ← this]; ring⟩
  obtain ⟨q, hq⟩ : MvPolynomial.C ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← Set.image_singleton, ← Ideal.map_span, MvPolynomial.mem_map_C_iff]
    intro s
    exact Ideal.mem_span_singleton.mpr (hc s)
  refine ⟨q, ?_⟩
  rw [hX]
  ext s
  have e := congrArg (MvPolynomial.coeff s)
    (show MvPolynomial.C ϖ * (q * (MvPolynomial.monomial d 1 - MvPolynomial.C ϖ)) = MvPolynomial.C ϖ * g by
      rw [← hp, hq]; ring)
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hϖ).mp e

end Model

end GlobalTheory.LogCris
