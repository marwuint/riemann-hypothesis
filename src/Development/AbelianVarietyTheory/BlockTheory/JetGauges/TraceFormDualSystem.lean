import Mathlib

open NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

section Forms

variable (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]

def balancedForms : Submodule ℝ (Y →+ Y →+ ℝ) where
  carrier := {β | (∀ x x', β x x' = β x' x) ∧
    ∀ (a : 𝓞 E) (x x' : Y), β (a • x) x' = β x (bar E a • x')}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.add_apply]; rw [h1, k1]
    · simp only [AddMonoidHom.add_apply]; rw [h2, k2]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨h1, h2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.smul_apply]; rw [h1]
    · simp only [AddMonoidHom.smul_apply]; rw [h2]

variable {E Y}

noncomputable def quad (β : balancedForms E Y) (x : Y) : ℝ := β.1 x x / 2

def IsPosSemidef (β : balancedForms E Y) : Prop := ∀ x : Y, 0 ≤ β.1 x x

def IsPosDef (β : balancedForms E Y) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Y), LinearIndependent ℤ x →
    ∀ t : Fin n → ℝ, t ≠ 0 → 0 < ∑ i, ∑ j, t i * t j * β.1 (x i) (x j)

variable (E Y)

structure Exponent where

  form : Module.Dual (𝓞 E) Y →+ Module.Dual (𝓞 E) Y →+ 𝓞 E
  smul_left : ∀ (a : 𝓞 E) y y', form (a • y) y' = a * form y y'
  hermitian : ∀ y y', form y' y = bar E (form y y')
  pos : ∀ (τ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (τ ((form y y : 𝓞 E) : E)).re

variable {E Y}

variable (E Y)

structure DualSystem where

  n : ℕ

  e : Fin n → Y

  y : Fin n → Module.Dual (𝓞 E) Y
  expand : ∀ x, ∑ j, y j x • e j = x

theorem nonempty_dualSystem [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] :
    Nonempty (DualSystem E Y) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Y
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨⟨n, fun j => f (fun k => if j = k then 1 else 0), fun j => LinearMap.proj j ∘ₗ s,
    fun x => ?_⟩⟩
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  calc _ = f (s x) := (LinearMap.pi_apply_eq_sum_univ f (s x)).symm
    _ = x := hx

variable {E Y}

noncomputable def DualSystem.pairing (D : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) : ℝ :=
  (∑ j, ∑ k, β.1 (l.form (D.y j) (D.y k) • D.e j) (D.e k)) / 2

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

noncomputable def pairing (l : Exponent E Y) (β : balancedForms E Y) : ℝ :=
  (Classical.choice (nonempty_dualSystem E Y)).pairing l β

def pairingValues (β : balancedForms E Y) : Set ℝ := Set.range fun l : Exponent E Y => pairing l β

def IsPhiC (β : balancedForms E Y) (r : ℝ) : Prop := IsLeast (pairingValues β) r

end Forms

end GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem
