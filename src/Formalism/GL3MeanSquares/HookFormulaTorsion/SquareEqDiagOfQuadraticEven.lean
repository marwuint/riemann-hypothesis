import Mathlib
import Formalism.GL3MeanSquares.SignsFromTrianglesSquares

open Finset

namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower

open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity

theorem t_heis : HeisenbergCocycle := by
  intro V _ H hadd hherm F x y z
  have hadd2 : ∀ x y y', H x (y + y') = H x y + H x y' := by
    intro x y y'; rw [hherm (y+y') x, hadd, map_add, ← hherm, ← hherm]
  have hc : H y x = H x y - 2 * Complex.I * ((H x y).im : ℂ) := by
    rw [hherm x y]; apply Complex.ext <;> simp <;> ring
  unfold Heisenberg₂
  rw [add_assoc, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hadd, hadd2]
  rw [hc]
  ring

end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower

namespace Formalism.HermitianLattices.WeilRepresentation

theorem heisenberg_cocycle : HeisenbergCocycle := CocycleEighthPower.t_heis
end Formalism.HermitianLattices.WeilRepresentation
