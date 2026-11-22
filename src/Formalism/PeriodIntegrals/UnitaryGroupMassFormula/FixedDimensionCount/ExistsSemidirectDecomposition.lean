import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim

noncomputable section

namespace PI.UnitaryGroupMassFormula.DiaFixDim.Main

open Formalism.UG Formalism.L2.SG.ClassAct Module

def dk {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) : Subgroup G where
  carrier := {g | ∃ δ ∈ D, ∃ κ ∈ K, g = δ * κ}
  one_mem' := ⟨1, D.one_mem, 1, K.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨δ, hδ, κ, hκ, rfl⟩ ⟨δ', hδ', κ', hκ', rfl⟩
    exact ⟨δ * δ', D.mul_mem hδ hδ', (δ'⁻¹ * κ * δ') * κ',
      K.mul_mem (hN.inv_conj hδ' hκ) hκ', by group⟩
  inv_mem' := by
    rintro _ ⟨δ, hδ, κ, hκ, rfl⟩
    exact ⟨δ⁻¹, D.inv_mem hδ, δ * κ⁻¹ * δ⁻¹, hN δ hδ _ (K.inv_mem hκ), by group⟩

end PI.UnitaryGroupMassFormula.DiaFixDim.Main
