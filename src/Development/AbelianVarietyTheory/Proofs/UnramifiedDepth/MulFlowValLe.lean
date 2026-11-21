import Mathlib
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowScaling

variable {l d : ℕ} [NeZero d]

lemma isFlow_zero {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

lemma mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith

lemma flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx

lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact flowVal_le hl hy

lemma maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy

lemma maxFlow_le_div (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx

lemma maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this

lemma mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by
  rcases hc.eq_or_lt with rfl | hc0
  · rw [zero_mul]
    exact maxFlow_nonneg hl fun a => by simpa using h a
  · rw [← le_div_iff₀' hc0]
    refine maxFlow_le hD fun x hx => ?_
    rw [le_div_iff₀' hc0]
    have hf : IsFlow l d D' (fun a i => c * x a i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_)
        ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hv : flowVal d (fun a i => c * x a i) = c * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [← hv]
    exact le_maxFlow hl hf

lemma maxFlow_mul (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this

end GlobalTheory.FlowScaling
