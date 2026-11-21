import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.L2.SG.ClassAct

open Formalism.UG Module

section Abstract

variable {G : Type} [Group G]

def Normalises (D K : Subgroup G) : Prop := ∀ δ ∈ D, ∀ κ ∈ K, δ * κ * δ⁻¹ ∈ K

theorem Normalises.inv_conj {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by
  have := h δ⁻¹ (D.inv_mem hδ) κ hκ
  simpa using this

def AMFChi (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) : Submodule k (G → W) where
  carrier := {f | ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ((χ κ : kˣ) : k) • ρ γ (f g)}
  zero_mem' := by intro γ g κ; simp
  add_mem' := by
    intro f f' hf hf' γ g κ
    simp only [Pi.add_apply, hf γ g κ, hf' γ g κ, map_add, smul_add]
  smul_mem' := by
    intro c f hf γ g κ
    simp only [Pi.smul_apply, hf γ g κ, map_smul]
    rw [smul_comm]

end Abstract

end Formalism.L2.SG.ClassAct
