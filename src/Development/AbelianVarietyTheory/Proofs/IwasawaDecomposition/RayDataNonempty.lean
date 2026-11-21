import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

noncomputable section

namespace GlobalTheory.Mem.RayEx

open NumberField IsDedekindDomain

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)

def Rel (I J : Ideal R) : Prop :=
  ∃ a b : R, a - 1 ∈ m ∧ b - 1 ∈ m ∧ Ideal.span {a} * I = Ideal.span {b} * J

variable {m}

theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ m) (hb : b - 1 ∈ m) : a * b - 1 ∈ m := by
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  exact m.add_mem (m.mul_mem_left _ hb) ha

theorem Rel.refl (I : Ideal R) : Rel m I I := ⟨1, 1, by simp, by simp, rfl⟩

theorem Rel.symm {I J : Ideal R} (h : Rel m I J) : Rel m J I := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  exact ⟨b, a, hb, ha, h.symm⟩

theorem Rel.mul {I J I' J' : Ideal R} (h : Rel m I J) (h' : Rel m I' J') : Rel m (I * I') (J * J') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨a * c, b * d, mul_sub_one_mem ha hc, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, h, h', mul_mul_mul_comm]

theorem Rel.trans {I J L : Ideal R} (h : Rel m I J) (h' : Rel m J L) : Rel m I L := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨c * a, b * d, mul_sub_one_mem hc ha, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_assoc, h, mul_left_comm, h', mul_assoc]

end General

end GlobalTheory.Mem.RayEx

end
