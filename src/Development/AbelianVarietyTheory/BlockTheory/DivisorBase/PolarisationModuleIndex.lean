import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

variable {E : Type} [Field E] [NumberField E]

def latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : Submodule (OF E) E where
  carrier := lattice c y
  zero_mem' := (latticeSub c y).zero_mem
  add_mem' := fun ha hb => (latticeSub c y).add_mem ha hb
  smul_mem' := fun a x hx => by
    rw [Algebra.smul_def]
    exact mul_mem_lattice (algebraMap_mem_orderC c a) hx

@[simp] theorem coe_latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : (latMod c y : Set E) = lattice c y := rfl

def TrInt (x : E) : Prop := ∃ n : ℤ, Algebra.trace ℚ E x = n

theorem TrInt.zero : TrInt (0 : E) := ⟨0, by simp⟩

theorem TrInt.add {x y : E} (hx : TrInt x) (hy : TrInt y) : TrInt (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, by rw [map_add, hm, hn]; push_cast; rfl⟩

variable [IsCMField E]

abbrev bar (x : E) : E := IsCMField.complexConj E x

theorem bar_algebraMap (a : OF E) : bar (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
  (IsCMField.complexConj E).commutes (a : maximalRealSubfield E)

def dualLat (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {z | ∀ x ∈ L, TrInt (z * bar x)}
  zero_mem' := fun x _ => by rw [zero_mul]; exact TrInt.zero
  add_mem' := fun ha hb x hx => by rw [add_mul]; exact (ha x hx).add (hb x hx)
  smul_mem' := fun a z hz x hx => by
    have h := hz (a • x) (L.smul_mem a hx)
    have e : z * bar (a • x) = a • z * bar x := by
      rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, bar_algebraMap]; ring
    rwa [e] at h

def polMod (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {ξ | bar ξ = -ξ ∧ ∀ x ∈ L, ∀ y ∈ L, TrInt (ξ * x * bar y)}
  zero_mem' := ⟨by simp, fun x _ y _ => by rw [zero_mul, zero_mul]; exact TrInt.zero⟩
  add_mem' := fun {a b} ha hb => ⟨by
      have h1 := ha.1
      have h2 := hb.1
      simp only [bar] at h1 h2 ⊢
      rw [map_add, h1, h2]; ring,
    fun x hx y hy => by rw [add_mul, add_mul]; exact (ha.2 x hx y hy).add (hb.2 x hx y hy)⟩
  smul_mem' := fun a ξ hξ => ⟨by
      have h1 := hξ.1
      rw [Algebra.smul_def, bar, map_mul, ← bar, ← bar, bar_algebraMap, h1]; ring,
    fun x hx y hy => by
      have h := hξ.2 (a • x) (L.smul_mem a hx) y hy
      have e : ξ * (a • x) = a • ξ * x := by rw [Algebra.smul_def, Algebra.smul_def]; ring
      rwa [e] at h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
