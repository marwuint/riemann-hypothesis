import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open NumberField

def Tor (q : ℕ) (L : PeriodPair) : Set ℂ := {z | ∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ (m : ℂ) * z ∈ L.lattice}

structure TorIso (K : IntermediateField ℚ ℂ) (q : ℕ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  maps : ∀ z ∈ Tor q L, θ z ∈ Tor q L'
  add : ∀ z ∈ Tor q L, ∀ w ∈ Tor q L, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z ∈ Tor q L, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w ∈ Tor q L', ∃ z ∈ Tor q L, θ z - w ∈ L'.lattice
  lin : ∀ (a : 𝓞 K), ∀ z ∈ Tor q L, θ (((a : K) : ℂ) * z) - ((a : K) : ℂ) * θ z ∈ L'.lattice

structure Transp (σ : ℂ ≃+* ℂ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  g2 : L'.g₂ = σ L.g₂
  g3 : L'.g₃ = σ L.g₃
  add : ∀ z w, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w, ∃ z, θ z - w ∈ L'.lattice
  wp : ∀ z, z ∉ L.lattice → L'.weierstrassP (θ z) = σ (L.weierstrassP z)
  wp' : ∀ z, z ∉ L.lattice → L'.derivWeierstrassP (θ z) = σ (L.derivWeierstrassP z)

end GlobalTheory.CMRam
