import Mathlib
import GroundTheory.TateCohomology.CoresRes
import GroundTheory.TateCohomology.TateLow

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

section Invariants

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

def invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) : (res f A).ρ.invariants :=
  ⟨x, fun h => x.2 (f h)⟩

@[simp]
lemma coe_invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) :
    (invariantsRes f x : A) = x := rfl

variable (S : Subgroup G) {A : Rep.{u} k G}

lemma ρ_mul_of_mem (y : (res S.subtype A).ρ.invariants) (g : G) {s : G} (hs : s ∈ S) :
    A.ρ (g * s) (y : A) = A.ρ g y := by
  rw [map_mul, Module.End.mul_apply]
  exact congrArg (A.ρ g) (y.2 ⟨s, hs⟩)

def cosetSMul (y : (res S.subtype A).ρ.invariants) (q : G ⧸ S) : A :=
  Quotient.liftOn' q (fun g => A.ρ g y) fun g g' h => by
    rw [QuotientGroup.leftRel_apply] at h
    rw [← ρ_mul_of_mem S y g h, mul_inv_cancel_left]

@[simp]
lemma cosetSMul_mk (y : (res S.subtype A).ρ.invariants) (g : G) :
    cosetSMul S y (g : G ⧸ S) = A.ρ g y := rfl

lemma cosetSMul_smul (y : (res S.subtype A).ρ.invariants) (h : G) (q : G ⧸ S) :
    cosetSMul S y (h • q) = A.ρ h (cosetSMul S y q) := by
  induction q using QuotientGroup.induction_on with | H g =>
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, cosetSMul_mk, cosetSMul_mk, map_mul,
    Module.End.mul_apply]

variable [Fintype G]

open scoped Classical in

noncomputable def transferSum (y : (res S.subtype A).ρ.invariants) : A :=
  ∑ q : G ⧸ S, cosetSMul S y q

lemma transferSum_mem_invariants (y : (res S.subtype A).ρ.invariants) :
    transferSum S y ∈ A.ρ.invariants := fun h => by
  classical
  simp only [transferSum, map_sum]
  rw [show (∑ q : G ⧸ S, A.ρ h (cosetSMul S y q)) = ∑ q : G ⧸ S, cosetSMul S y (h • q) from
    Finset.sum_congr rfl fun q _ => (cosetSMul_smul S y h q).symm]
  exact Fintype.sum_equiv (MulAction.toPerm h) _ _ fun _ => rfl

noncomputable def transferInv (y : (res S.subtype A).ρ.invariants) : A.ρ.invariants :=
  ⟨transferSum S y, transferSum_mem_invariants S y⟩

@[simp]
lemma coe_transferInv (y : (res S.subtype A).ρ.invariants) :
    (transferInv S y : A) = transferSum S y := rfl

end Invariants

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

def coindConst (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (coind S.subtype B).ρ.invariants :=
  ⟨⟨fun _ => y, (Representation.mem_coindV _ _ _).2 fun s _ => (y.2 s).symm⟩,
    fun _ => rfl⟩

@[simp]
lemma coindConst_apply (B : Rep.{u} k S) (y : B.ρ.invariants) (g : G) :
    ((coindConst S B y : coind S.subtype B) : G → B) g = y := rfl

variable [Fintype G] [Fintype S]

end Shapiro

end GroundTheory.GroupCoh
