import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport
import Formalism.LatticeTheta.ThetaShiftInversion

open Module

noncomputable section

namespace PI.Tr

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dualLat_eq (Λ : Submodule ℤ E) :
    dualLat Λ = LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  show (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) ↔ _
  refine forall₂_congr fun x _ => ?_
  rw [innerₗ_apply_apply, real_inner_comm, Submodule.mem_one]
  simp only [algebraMap_int_eq, eq_intCast]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

section lattice

variable [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

instance instDiscreteDualLat : DiscreteTopology (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [dualLat_eq]
  exact (Formalism.H.dualIsLattice E Λ).1

instance instIsZLatticeDualLat : IsZLattice ℝ (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have h := Formalism.H.dualIsLattice E Λ
  haveI := h.1
  have h2 : IsZLattice ℝ (Formalism.H.dual Λ) := h.2
  constructor
  rw [dualLat_eq]
  exact h2.span_top

end lattice

end PI.Tr
