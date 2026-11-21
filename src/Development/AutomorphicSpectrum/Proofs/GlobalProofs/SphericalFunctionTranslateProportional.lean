import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphericalRep

open Topology

section Alg

variable {G : Type} [Group G]

def translates (φ : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun (x : G) (g : G) => φ (g * x))

def rightTr (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => f (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rightTr_apply (h : G) (f : G → ℂ) (g : G) : rightTr h f g = f (g * h) := rfl

theorem gen_mem (φ : G → ℂ) (x : G) : (fun g => φ (g * x)) ∈ translates φ :=
  Submodule.subset_span ⟨x, rfl⟩

theorem rightTr_mem (φ : G → ℂ) (h : G) {f : G → ℂ} (hf : f ∈ translates φ) :
    rightTr h f ∈ translates φ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    have : rightTr h (fun g => φ (g * x)) = fun g => φ (g * (h * x)) := by
      funext g; simp [mul_assoc]
    rw [this]; exact gen_mem φ _
  | zero => simp
  | add f f' _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c f _ h1 => rw [map_smul]; exact Submodule.smul_mem _ _ h1

def rightEquiv (φ : G → ℂ) (h : G) : translates φ ≃ₗ[ℂ] translates φ where
  toFun f := ⟨rightTr h f.1, rightTr_mem φ h f.2⟩
  invFun f := ⟨rightTr h⁻¹ f.1, rightTr_mem φ h⁻¹ f.2⟩
  map_add' f f' := by ext g; simp
  map_smul' c f := by ext g; simp
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp

@[simp] theorem rightEquiv_coe (φ : G → ℂ) (h : G) (f : translates φ) (g : G) :
    (rightEquiv φ h f : G → ℂ) g = (f : G → ℂ) (g * h) := rfl

end Alg

end GlobalTheory.CompanionTheory.SphericalRep
