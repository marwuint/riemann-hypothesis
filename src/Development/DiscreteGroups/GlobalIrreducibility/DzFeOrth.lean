import Mathlib

noncomputable section

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime]

def psiC (ψ₀ : AddChar (ZMod g) Circle) : AddChar (ZMod g) ℂ where
  toFun x := (ψ₀ x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem psiC_apply (ψ₀ : AddChar (ZMod g) Circle) (x : ZMod g) : psiC ψ₀ x = (ψ₀ x : ℂ) := rfl

end DiscreteGroups.sglob.DzFe
