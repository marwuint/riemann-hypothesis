import Mathlib
import GroundTheory.PAdicHodge.SemilinearResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WittLift

open WittVector Finset Matrix

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*}

local notation "𝕎" => WittVector p

section Perfect

variable [CommRing k] [CharP k p] [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in
theorem sMod_iff (x y : 𝕎 k) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {(p : 𝕎 k)}) ^ n • ⊤ : Submodule (𝕎 k) (𝕎 k))] ↔
      x - y ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]

theorem exists_limit (a : ℕ → 𝕎 k) (h : ∀ n, a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ n}) :
    ∃ L, ∀ n, L - a n ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  have hmono : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {(p : 𝕎 k) ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ m} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hmn) (h n)
      have := Ideal.add_mem _ ih h1
      convert this using 1
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : 𝕎 k)}) a (fun {m n} hmn => by
    rw [sMod_iff, ← neg_sub]
    exact neg_mem (hmono m n hmn))
  refine ⟨L, fun n => ?_⟩
  have := (sMod_iff _ _ _).mp (hL n)
  rw [← neg_sub]
  exact neg_mem this

theorem eq_zero_of_forall_mem (x : 𝕎 k) (h : ∀ n, x ∈ Ideal.span {(p : 𝕎 k) ^ n}) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : 𝕎 k)}) x (fun n => by
    rw [sMod_iff, sub_zero]
    exact h n)

end Perfect

section Matrix

variable [CommRing k] [CharP k p] {ι : Type*} [Fintype ι]

noncomputable def matOp (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) :
    (ι → 𝕎 k) →+ (ι → 𝕎 k) where
  toFun x := A *ᵥ (fun i => τ (x i))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero A
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

omit [CharP k p] in
theorem matOp_apply (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) (x : ι → 𝕎 k) :
    matOp A τ x = A *ᵥ (fun i => τ (x i)) := rfl

variable {e : ℕ}

noncomputable def resOp (A : Matrix ι ι (𝕎 k)) (e : ℕ) : (ι → k) →+ (ι → k) where
  toFun x := A.map (fun a => a.coeff 0) *ᵥ (fun i => x i ^ p ^ e)
  map_zero' := by
    rw [← Matrix.mulVec_zero (A.map (fun a => a.coeff 0))]
    congr 1
    funext i
    simp [hp.out.ne_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [add_pow_char_pow]

variable [PerfectRing k p]

end Matrix

end WittLift

end GroundTheory.PAdicHodge
