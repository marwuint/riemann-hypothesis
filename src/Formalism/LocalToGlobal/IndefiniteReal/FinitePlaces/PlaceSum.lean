import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceInst

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem psi_neg_one (ψ : AddChar (AF D.host.F) ℂ) {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

end Formalism.IndefR.Fin

end
