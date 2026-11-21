import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
import GroundTheory.PAdicHodge.SemilinearResidue
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace DMTeich

open TeichLift Finset Matrix

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

variable (T) in

theorem isUnit_of_red_ne_zero {x : Γ} (hx : T.red x ≠ 0) : IsUnit x := by
  have h1 : T.coeff (T.teich (T.red x)⁻¹ * x) 0 = 1 := by
    rw [T.coeff_teich_mul, T.coeff_zero, inv_mul_cancel₀ hx]
  exact isUnit_of_mul_isUnit_right (T.isUnit_of_coeff_zero_eq_one h1)

theorem nontrivial_Γ (T : TeichLift p L Γ) : Nontrivial Γ :=
  ⟨⟨0, 1, fun h => by have := congrArg T.red h; simp at this⟩⟩

variable (T) in

theorem isField_B : IsField T.B where
  exists_pair_ne := by have := T.nontrivial_B; exact ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro b hb
    obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact hb (T.eq_zero_of_mul_pow hx)
    obtain ⟨m, x', hxx', hx'0, -⟩ := T.exists_eq_π_pow_mul hx0
    obtain ⟨y, hy⟩ := (isUnit_of_red_ne_zero T hx'0).exists_right_inv
    refine ⟨algebraMap Γ T.B (T.π ^ N * y) * IsLocalization.Away.invSelf T.π ^ m, ?_⟩
    have hinv : algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π = 1 :=
      IsLocalization.Away.mul_invSelf T.π
    calc b * (algebraMap Γ T.B (T.π ^ N * y) * IsLocalization.Away.invSelf T.π ^ m)
        = (b * algebraMap Γ T.B T.π ^ N) * algebraMap Γ T.B y *
            IsLocalization.Away.invSelf T.π ^ m := by rw [map_mul, map_pow]; ring
      _ = algebraMap Γ T.B (x' * y) *
            (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ m := by
          simp only [hx, hxx', map_mul, map_pow]; ring
      _ = 1 := by rw [hy, map_one, hinv, one_pow, one_mul]

noncomputable instance instFieldB : Field T.B := (isField_B T).toField

structure FixedUnif (F : T.TeichFrob) where

  z : Γ
  isUnit_alt₂ : IsUnit z
  φ_fix : F.φ (T.π * z) = T.π * z
  a_pos : 0 < F.a

namespace FixedUnif

variable {F : T.TeichFrob} (U : FixedUnif F)

def ϖ0 : Γ := T.π * U.z

def ϖ : T.B := algebraMap Γ T.B U.ϖ0

theorem ϖ0_mem_nonZeroDivisors : U.ϖ0 ∈ nonZeroDivisors Γ :=
  mul_mem T.π_mem_nonZeroDivisors U.isUnit_alt₂.mem_nonZeroDivisors

theorem ϖ0_ne_zero : U.ϖ0 ≠ 0 := by
  have := nontrivial_Γ T
  exact nonZeroDivisors.ne_zero U.ϖ0_mem_nonZeroDivisors

theorem ϖ_ne_zero : U.ϖ ≠ 0 := fun h =>
  U.ϖ0_ne_zero (T.algebraMap_injective (by rw [map_zero]; exact h))

theorem algebraMap_ϖ0 : algebraMap Γ T.B U.ϖ0 = U.ϖ := rfl

end FixedUnif

variable {F : T.TeichFrob} (U : FixedUnif F)

open FixedUnif

def IsInt (n : ℤ) (a : T.B) : Prop :=
  ∃ w : Γ, a = U.ϖ ^ n * algebraMap Γ T.B w

variable {U}

theorem isInt_zero (n : ℤ) : IsInt U n 0 := ⟨0, by simp⟩

theorem IsInt.add {n : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U n b) :
    IsInt U n (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, by rw [map_add, mul_add]⟩

theorem IsInt.neg {n : ℤ} {a : T.B} (ha : IsInt U n a) : IsInt U n (-a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨-x, by rw [map_neg, mul_neg]⟩

theorem IsInt.sub {n : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U n b) :
    IsInt U n (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem IsInt.mul {n m : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U m b) :
    IsInt U (n + m) (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, by rw [zpow_add₀ U.ϖ_ne_zero, map_mul]; ring⟩

theorem IsInt.mono {n m : ℤ} {a : T.B} (h : m ≤ n) (ha : IsInt U n a) : IsInt U m a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n = m + t := ⟨(n - m).toNat, by omega⟩
  refine ⟨U.ϖ0 ^ t * x, ?_⟩
  rw [ht, zpow_add₀ U.ϖ_ne_zero, map_mul, map_pow, algebraMap_ϖ0, zpow_natCast]
  ring

theorem IsInt.sum {n : ℤ} {ι : Type*} (s : Finset ι) (f : ι → T.B)
    (h : ∀ i ∈ s, IsInt U n (f i)) : IsInt U n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInt_zero n
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Matrix

variable {ι : Type*}

variable [Fintype ι]

noncomputable def matOp (A : Matrix ι ι Γ) (τ : Γ →+* Γ) : (ι → Γ) →+ (ι → Γ) where
  toFun x := A *ᵥ (fun i => τ (x i))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero A
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem matOp_apply (A : Matrix ι ι Γ) (τ : Γ →+* Γ) (x : ι → Γ) :
    matOp A τ x = A *ᵥ (fun i => τ (x i)) := rfl

variable {e : ℕ}

variable (T) in

noncomputable def resOp (A : Matrix ι ι Γ) (e : ℕ) : (ι → L) →+ (ι → L) where
  toFun x := A.map T.red *ᵥ (fun i => x i ^ p ^ e)
  map_zero' := by
    rw [← Matrix.mulVec_zero (A.map T.red)]
    congr 1
    funext i
    simp [hp.out.ne_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [add_pow_char_pow]

theorem resOp_apply (A : Matrix ι ι Γ) (x : ι → L) :
    resOp T A e x = A.map T.red *ᵥ (fun i => x i ^ p ^ e) := rfl

variable [IsAlgClosed L]

end Matrix

end DMTeich

end GroundTheory.PAdicHodge
