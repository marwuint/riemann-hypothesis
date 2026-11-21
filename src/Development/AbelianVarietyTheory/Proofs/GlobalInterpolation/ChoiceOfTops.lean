import Mathlib
import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

noncomputable section

open scoped BigOperators
open Finset Formalism.G0

namespace GlobalTheory.RandomTops

def ex (δ : ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, δ ^ T.card * (1 - δ) ^ (S.card - T.card) * f T

open Classical in

def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind
  rw [if_pos h]
theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  rw [if_neg h]
theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  unfold ind
  split_ifs <;> norm_num
theorem ind_le {p : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : p → 1 ≤ x) : ind p ≤ x := by
  unfold ind
  split_ifs with hp
  · exact h1 hp
  · exact h0
theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by
  rw [h]

variable {δ : ℝ}

theorem ex_empty (f : Finset ℕ → ℝ) : ex δ ∅ f = f ∅ := by
  simp [ex]

theorem ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    ex δ (insert a S) f = (1 - δ) * ex δ S f + δ * ex δ S (fun T => f (insert a T)) := by
  unfold ex
  rw [sum_powerset_insert ha, card_insert_of_notMem ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have := card_le_card (mem_powerset.mp hT)
    rw [show #S + 1 - #T = (#S - #T) + 1 by omega, pow_succ]
    ring
  · refine sum_congr rfl fun T hT => ?_
    have hT' : a ∉ T := fun h => ha (mem_powerset.mp hT h)
    rw [card_insert_of_notMem hT', show #S + 1 - (#T + 1) = #S - #T by omega, pow_succ]
    ring

theorem ex_congr {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    ex δ S f = ex δ S g := by
  unfold ex
  exact sum_congr rfl fun T hT => by rw [h T (mem_powerset.mp hT)]

theorem ex_const (S : Finset ℕ) (c : ℝ) : ex δ S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => simp [ex_empty]
  | insert a S ha ih => rw [ex_insert ha, ih]; ring

theorem ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => c * f T) = c * ex δ S f := by
  unfold ex
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    ex δ S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, ex δ S (f i) := by
  unfold ex
  simp only [mul_sum]
  rw [sum_comm]

theorem ex_mono (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {S : Finset ℕ} {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : ex δ S f ≤ ex δ S g := by
  unfold ex
  refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (h T (mem_powerset.mp hT)) ?_
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

theorem ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    ex δ (A ∪ B) f = ex δ A (fun T => ex δ B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp [ex_empty]
  | insert a A ha ih =>
    have haB : a ∉ B := fun h => disjoint_left.mp hAB (mem_insert_self a A) h
    have hAB' : Disjoint A B := disjoint_of_subset_left (subset_insert a A) hAB
    have haU : a ∉ A ∪ B := by simp [ha, haB]
    rw [insert_union, ex_insert haU, ex_insert ha, ih hAB', ih hAB']
    simp only [insert_union]

theorem ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A) * g (T \ A)) = ex δ A f * ex δ (S \ A) g := by
  have hd : Disjoint A (S \ A) := disjoint_sdiff
  conv_lhs => rw [← union_sdiff_of_subset hA]
  rw [ex_union hd]
  have e : ∀ T ⊆ A, ex δ (S \ A) (fun U => f ((T ∪ U) ∩ A) * g ((T ∪ U) \ A)) =
      f T * ex δ (S \ A) g := by
    intro T hT
    rw [← ex_mul_left]
    refine ex_congr fun U hU => ?_
    have e1 : (T ∪ U) ∩ A = T := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_inter, mem_union, mem_sdiff] at *
      tauto
    have e2 : (T ∪ U) \ A = U := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_union, mem_sdiff] at *
      tauto
    rw [e1, e2]
  rw [ex_congr e]
  have := ex_mul_left (δ := δ) A (ex δ (S \ A) g) f
  rw [mul_comm, ← this]
  congr 1
  funext T
  ring

theorem ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A)) = ex δ A f := by
  have h := ex_split (δ := δ) hA f (fun _ => 1)
  simp only [mul_one, ex_const] at h
  exact h

theorem ex_contains {Q B : Finset ℕ} (hQ : Q ⊆ B) :
    ex δ B (fun T => ind (Q ⊆ T)) = δ ^ Q.card := by
  have e : ex δ B (fun T => ind (Q ⊆ T)) = ex δ B (fun T => ind (Q ⊆ T ∩ Q)) :=
    ex_congr fun T _ => ind_congr (by simp [subset_inter_iff])
  rw [e, ex_restrict hQ (fun T => ind (Q ⊆ T))]
  unfold ex
  rw [sum_eq_single Q]
  · beta_reduce
    rw [ind_pos subset_rfl]
    simp
  · intro T hT hne
    beta_reduce
    rw [ind_neg, mul_zero]
    exact fun h => hne (subset_antisymm (mem_powerset.mp hT) h)
  · intro h
    exact absurd (mem_powerset_self Q) h

theorem tail_le_choose (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {B : Finset ℕ} {L : ℕ} (hB : B.card ≤ L) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) ≤ (L.choose K : ℝ) * δ ^ K := by
  have hpt : ∀ T ⊆ B, ind (K ≤ #T) ≤ ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T) := by
    intro T hT
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hK => ?_
    obtain ⟨Q, hQT, hQ⟩ := Finset.exists_subset_card_eq hK
    have hQB : Q ∈ B.powersetCard K := mem_powersetCard.mpr ⟨hQT.trans hT, hQ⟩
    calc (1 : ℝ) = ind (Q ⊆ T) := (ind_pos hQT).symm
      _ ≤ _ := single_le_sum (f := fun Q => ind (Q ⊆ T)) (fun _ _ => ind_nonneg _) hQB
  calc ex δ B (fun T => ind (K ≤ #T))
      ≤ ex δ B (fun T => ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T)) := ex_mono h0 h1 hpt
    _ = ∑ Q ∈ B.powersetCard K, ex δ B (fun T => ind (Q ⊆ T)) :=
      ex_sum _ _ (fun Q T => ind (Q ⊆ T))
    _ = ∑ Q ∈ B.powersetCard K, δ ^ K := sum_congr rfl fun Q hQ => by
      rw [ex_contains (mem_powersetCard.mp hQ).1, (mem_powersetCard.mp hQ).2]
    _ = ((#B).choose K : ℝ) * δ ^ K := by rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (L.choose K : ℝ) * δ ^ K :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose K hB) (pow_nonneg h0 _)

theorem tail_eq (B : Finset ℕ) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) = binUpper B.card δ K := by
  unfold ex binUpper
  have hs := sum_powerset_apply_card (fun m => δ ^ m * (1 - δ) ^ (#B - m) * ind (K ≤ m)) (x := B)
  rw [hs]
  have hI : Icc K #B = (range (#B + 1)).filter (fun m => K ≤ m) := by
    ext m
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [hI, sum_filter]
  refine sum_congr rfl fun m _ => ?_
  unfold ind
  split_ifs
  · rw [nsmul_eq_mul]
    ring
  · simp

theorem tail_le_binUpper (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ} {G : ℕ} (hA : A.card ≤ G)
    (K : ℕ) : ex δ A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  obtain ⟨A', hAA', hA'⟩ := Infinite.exists_superset_card_eq A G hA
  calc ex δ A (fun T => ind (K ≤ #T)) = ex δ A' (fun T => ind (K ≤ #(T ∩ A))) :=
      (ex_restrict hAA' (fun T => ind (K ≤ #T))).symm
    _ ≤ ex δ A' (fun T => ind (K ≤ #T)) := ex_mono h0 h1 fun T _ =>
      ind_le (ind_nonneg _) fun h => (ind_pos (le_trans h (card_le_card inter_subset_left))).ge
    _ = binUpper G δ K := by rw [tail_eq, hA']

def tile (r u s : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))

theorem cell_subset {r u s c : ℕ} (hc : c ≤ 6 * r + 1) : cell r u s c ⊆ tile r u s := by
  intro x hx
  simp only [cell, tile, mem_Ico] at hx ⊢
  have : c * u ≤ (6 * r + 1) * u := Nat.mul_le_mul_right u hc
  constructor <;> nlinarith [hx.1, hx.2]

theorem cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by
  unfold cell
  rw [Nat.card_Ico]
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (c + 1) * u = c * u + u by ring, ← add_assoc, Nat.add_sub_cancel_left]

theorem ico_disjoint {a m i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ico (a + i * m) (a + (i + 1) * m)) (Finset.Ico (a + j * m) (a + (j + 1) * m)) := by
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (i + 1) * m ≤ j * m := Nat.mul_le_mul_right m h
    omega
  · have : (j + 1) * m ≤ i * m := Nat.mul_le_mul_right m h
    omega

theorem tile_disjoint {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  have := ico_disjoint (a := 0) (m := (6 * r + 1) * u) h
  simpa [tile] using this

theorem prod_alternate (a b : ℝ) (m : ℕ) :
    ∏ c ∈ Finset.range (2 * m + 1), (if Even c then a else b) = a ^ (m + 1) * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    have h2 : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      if_neg h1, if_pos h2]
    ring

theorem marked_congr {T T' : Finset ℕ} {r u s : ℕ} (h : T ∩ tile r u s = T' ∩ tile r u s)
    (hM : Marked T r u s) : Marked T' r u s := by
  intro c hc1 hc2
  have hsub := cell_subset (r := r) (u := u) (s := s) hc2
  have e : T ∩ cell r u s c = T' ∩ cell r u s c := by
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, h]
  rw [← e]
  exact hM c hc1 hc2

end GlobalTheory.RandomTops
