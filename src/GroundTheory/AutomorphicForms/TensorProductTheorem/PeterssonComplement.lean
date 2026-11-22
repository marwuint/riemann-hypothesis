import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

namespace PeterssonComplement

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)

def orthIn (U : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0}
  zero_mem' u _ := by rw [map_zero, inner_zero_right]
  add_mem' {v w} hv hw u hu := by rw [map_add, inner_add_right, hv u hu, hw u hu, add_zero]
  smul_mem' c v hv u hu := by rw [map_smul, inner_smul_right, hv u hu, mul_zero]

variable {ι}

theorem aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add, LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)

theorem apply_aeval_comm (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq

end PeterssonComplement

end GroundTheory.Automorphic
