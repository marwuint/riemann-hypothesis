import Formalism.WachModuleLifts.Statement

open Finset PowerSeries

noncomputable section

namespace Formalism.CL

namespace CSharpG

def Bd (p : ℕ) [Fact p.Prime] (α c : ℝ) (f : PowerSeries ℚ_[p]) : Prop :=
  ∀ b : ℕ, ‖coeff b f‖ ≤ (p : ℝ) ^ (α * b + c)

def Dg (p : ℕ) [Fact p.Prime] (D : ℕ) (f : PowerSeries ℚ_[p]) : Prop := ∀ b, D < b → coeff b f = 0

variable {p : ℕ} [hp : Fact p.Prime]

structure Level (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop where
  bd : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g)
  dg : Dg p (p ^ g) (uu p g)
  top : coeff (p ^ g) (uu p g) = (p : ℚ_[p])⁻¹
  c0 : coeff 0 (uu p g) = 0 ∨ coeff 0 (uu p g) = 1

end CSharpG

end Formalism.CL
