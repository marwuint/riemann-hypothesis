import Formalism.WachModuleLifts.StatementW

noncomputable section

namespace Formalism.CL.W

section Claim
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]

def QS (W : WachMod B η D) : Submodule ℤ_[p] D where
  carrier := {y | B.q ^ η • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.q ^ η • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.q ^ η • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.q ^ η • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy

end Claim

section Wit
open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev K := FractionRing (Polynomial ℤ_[p])

end Wit

end Formalism.CL.W
