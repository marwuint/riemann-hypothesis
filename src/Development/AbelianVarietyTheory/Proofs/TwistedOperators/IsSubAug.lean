import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.ThetaGLSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

variable {m : ℕ}

theorem om_add (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ + Ψ) = om μ g h Φ + om μ g h Ψ := by
  funext x; simp only [om, Pi.add_apply]; ring

theorem om_smul (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (c : ℂ) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x; simp only [om, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.ThetaGLSub
