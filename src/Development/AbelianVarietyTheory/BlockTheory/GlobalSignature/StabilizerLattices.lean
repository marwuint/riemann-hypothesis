import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers

open scoped TensorProduct Pointwise
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Lat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsSelfDualLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

variable (R : Type) [CommRing R] [Algebra F R]

def actV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  (h • (fun _ => y : Fin 1 → Fin M → R ⊗[F] E)) 0

theorem actV_eq (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) :
    actV R σ J h y = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec y := rfl

theorem actV_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (y : Fin M → R ⊗[F] E) : actV R σ J 1 y = y := by
  unfold actV
  rw [one_smul]

theorem actV_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : actV R σ J (g * h) y = actV R σ J g (actV R σ J h y) := by
  unfold actV
  rw [mul_smul]
  rfl

def stabLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Λ : AddSubgroup (Fin M → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {h | ∀ y, y ∈ Λ ↔ actV R σ J h y ∈ Λ}
  one_mem' := by intro y; rw [actV_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actV_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actV R σ J g⁻¹ y)
    rw [← actV_mul, mul_inv_cancel, actV_one] at this
    exact this.symm

end Lat

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P

def OrbitConcl (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))),
        actV (Af F) σ J k (fun i => inclR (F := F) (Af F) (x i)) = y) ∧
  ({h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x i)) ∈
        latHat F E (L : Set (Fin M → E))} =
      (Hstab (Af F) σ J (fun _ => x) : Set (HA (Af F) σ J)) *
        (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) : Set (HA (Af F) σ J))) ∧
  (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) ⊓ Hstab (Af F) σ J (fun _ => x) =
      stabLat (Af F) σ J (latHat F E (perpIn σ J L x)) ⊓ Hstab (Af F) σ J (fun _ => x))

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L →
    ∀ β : F, (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β → OrbitConcl F E σ J L x β

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers
