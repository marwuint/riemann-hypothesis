import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩

variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

end GlobalTheory.LocLanglands
