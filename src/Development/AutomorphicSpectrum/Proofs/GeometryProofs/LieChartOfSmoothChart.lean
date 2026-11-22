import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartDer

open scoped TensorProduct

theorem exists_diffModule {A B : Type} [CommRing A] [CommRing B] (g : B →+* A) (hg : g.Smooth)
    {R : Type} [CommRing R] (f : R) (u : A →+* Localization.Away f) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
      (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
      (_ : Module.Projective (Localization.Away f) P) (d : A → P),
      (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = u a • d b + u b • d a) ∧ (∀ b, d (g b) = 0) ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
        κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
        (∀ (w : P →ₗ[R] C) (r : Localization.Away f) (p : P), w (r • p) = κ r * w p) ∧
        (∀ w w' : P →ₗ[R] C, (∀ a, w (d a) = w' (d a)) → w = w') ∧
        (∀ δ : A → C, (∀ a b, δ (a + b) = δ a + δ b) →
          (∀ a b, δ (a * b) = κ (u a) * δ b + κ (u b) * δ a) → (∀ b, δ (g b) = 0) →
          ∃ w : P →ₗ[R] C, ∀ a, w (d a) = δ a) := by
  letI iB : Algebra B A := g.toAlgebra
  haveI : Algebra.Smooth B A := hg
  letI iA : Algebra A (Localization.Away f) := u.toAlgebra
  haveI tw : IsScalarTower R (Localization.Away f) (Localization.Away f ⊗[A] Ω[A⁄B]) := inferInstance
  have hsmul : ∀ (a : A) (x : Ω[A⁄B]), (1 : Localization.Away f) ⊗ₜ[A] (a • x) =
      u a • ((1 : Localization.Away f) ⊗ₜ[A] x) := fun a x => by
    have e : a • (1 : Localization.Away f) = u a := by
      rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [← TensorProduct.smul_tmul, e, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  refine ⟨Localization.Away f ⊗[A] Ω[A⁄B], inferInstance, inferInstance, inferInstance, tw,
    Module.Finite.base_change A _ _, inferInstance, fun a => 1 ⊗ₜ[A] KaehlerDifferential.D B A a,
    fun a b => by simp [TensorProduct.tmul_add], fun a b => ?_, fun b => ?_, ?_⟩
  · simp only [Derivation.leibniz, TensorProduct.tmul_add, hsmul]
  · have : g b = algebraMap B A b := rfl
    simp [this]
  intro C _ _ κ hκ
  letI aC : Algebra (Localization.Away f) C := κ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' hκ.symm
  have lin : ∀ (w : (Localization.Away f ⊗[A] Ω[A⁄B]) →ₗ[R] C) (r : Localization.Away f) p,
      w (r • p) = κ r * w p := fun w r p => by
    have h : w (r • p) = r • w p :=
      (w.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).map_smul r p
    rw [h, Algebra.smul_def]
    rfl
  refine ⟨lin, fun w w' h => LinearMap.ext fun p => ?_, fun δ h1 h2 h3 => ?_⟩
  · have hD : ∀ x : Ω[A⁄B], w ((1 : Localization.Away f) ⊗ₜ[A] x) = w' ((1 : Localization.Away f) ⊗ₜ[A] x) := by
      intro x
      have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D B A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul a x _ ih => rw [hsmul, lin, lin, ih]
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul r x =>
      have e : r ⊗ₜ[A] x = r • ((1 : Localization.Away f) ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, lin, lin, hD]
  · letI aA : Algebra A C := (κ.comp u).toAlgebra
    haveI : IsScalarTower A (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' rfl
    letI aB : Algebra B C := ((κ.comp u).comp g).toAlgebra
    haveI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
    let L : A →ₗ[B] C :=
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          change δ (g b * a) = κ (u (g b)) * δ a
          rw [h2, h3, mul_zero, add_zero] }
    let Dv : Derivation B A C := Derivation.mk' L fun a b => by
      change δ (a * b) = κ (u a) * δ b + κ (u b) * δ a
      exact h2 a b
    refine ⟨(Dv.liftKaehlerDifferential.liftBaseChange (Localization.Away f)).restrictScalars R, fun a => ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl

def dualOf {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C)
    (h1 : ∀ a b, δ (a + b) = δ a + δ b) (h2 : ∀ a b, δ (a * b) = v a * δ b + v b * δ a) :
    A →+* DualNumber C where
  toFun a := TrivSqZeroExt.inl (v a) + TrivSqZeroExt.inr (δ a)
  map_one' := by
    have h : δ 1 = 0 := by simpa using h2 1 1
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [h2, TrivSqZeroExt.snd_mul]
      ring
  map_zero' := by
    have h : δ 0 = 0 := by simpa using h1 0 0
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [h1]

theorem dualOf_fst {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).fst = v a := by
  simp [dualOf]

theorem dualOf_snd {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).snd = δ a := by
  simp [dualOf]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem one_left {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

end GlobalTheory.CompanionTheory.Ar.ChartDer
