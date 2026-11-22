import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.LocalFields.BrauerInductionElementary

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G]

section MulSubgroup

def mulSubgroup (C P : Subgroup G) (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) : Subgroup G where
  carrier := {h | ∃ c ∈ C, ∃ y ∈ P, h = c * y}
  one_mem' := ⟨1, C.one_mem, 1, P.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, y, hy, rfl⟩ ⟨c', hc', y', hy', rfl⟩
    refine ⟨c * c', C.mul_mem hc hc', y * y', P.mul_mem hy hy', ?_⟩
    rw [show c * y * (c' * y') = c * (y * c') * y' by group, ← hcomm c' hc' y hy]
    group
  inv_mem' := by
    rintro _ ⟨c, hc, y, hy, rfl⟩
    refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, P.inv_mem hy, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm c⁻¹ (C.inv_mem hc) y⁻¹ (P.inv_mem hy)).symm

theorem mem_mulSubgroup {C P : Subgroup G} {hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c} {h : G} :
    h ∈ mulSubgroup C P hcomm ↔ ∃ c ∈ C, ∃ y ∈ P, h = c * y := Iff.rfl

end MulSubgroup

variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)

def sylowCent : Subgroup G :=
  ((Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))) : Subgroup (Subgroup.centralizer {x})).map
    (Subgroup.centralizer {x}).subtype

variable {p x}

omit [Fintype G] hp in
theorem commute_of_mem_sylowCent {y : G} (hy : y ∈ sylowCent p x) : y * x = x * y := by
  have : y ∈ Subgroup.centralizer {x} := Subgroup.map_subtype_le _ hy
  exact Subgroup.mem_centralizer_singleton_iff.mp this

omit [Fintype G] hp in
theorem commute_zpowers_sylowCent :
    ∀ c ∈ Subgroup.zpowers x, ∀ y ∈ sylowCent p x, c * y = y * c := by
  intro c hc y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((Commute.symm (commute_of_mem_sylowCent hy)).zpow_left i).eq

variable (p x) in

def elemSub : Subgroup G := mulSubgroup (Subgroup.zpowers x) (sylowCent p x) commute_zpowers_sylowCent

variable (p x) in

abbrev sylowCentIn : Subgroup (elemSub p x) := (sylowCent p x).subgroupOf (elemSub p x)

instance normal_sylowCentIn : (sylowCentIn p x).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨c, hc, y, hy, hg⟩ := mem_mulSubgroup.mp g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
  have hw : y * n * y⁻¹ ∈ sylowCent p x :=
    (sylowCent p x).mul_mem ((sylowCent p x).mul_mem hy hn) ((sylowCent p x).inv_mem hy)
  rw [show c * y * (n : G) * (c * y)⁻¹ = c * (y * n * y⁻¹) * c⁻¹ by group,
    commute_zpowers_sylowCent c hc _ hw, mul_inv_cancel_right]
  exact hw

end GroundTheory.LocalField
