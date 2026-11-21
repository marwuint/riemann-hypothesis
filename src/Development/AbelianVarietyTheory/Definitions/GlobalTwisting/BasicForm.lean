import Mathlib

noncomputable section

open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

section Rel

variable {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

def gd (L : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) : P [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L X).restrictScalars ℝ).compAlternatingMap f
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L X Y) (f v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c X) (f v) }

end Rel

section Group

variable (𝕜 ι : Type) [RCLike 𝕜] [Fintype ι] (a : ℕ)

variable {𝕜 ι a}

def funRep {Γ : Type} [Group Γ] (Y : Type) [MulAction Γ Y] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ Γ (Y → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f y => ξ γ *ᵥ f (γ⁻¹ • y)
      map_add' := fun f g => funext fun y => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun y => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f y; simp
  map_mul' γ δ := by ext f y; simp [mul_smul]

end Group

end GlobalTheory.BorelCoh

end
