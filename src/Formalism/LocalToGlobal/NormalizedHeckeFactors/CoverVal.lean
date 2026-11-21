import Mathlib

namespace Formalism.L2.NCov

open Polynomial

section Val

variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

theorem nonneg_of_isIntegral {y : F} (hy : IsIntegral ℤ y) : 0 ≤ v y := by

  let w := AddValuation.toValuation v
  have h1 : IsIntegral w.integer y := IsIntegral.tower_top hy
  have h2 := (Valuation.integer.integers w).mem_of_integral h1
  exact h2

theorem withTop_add_pos {x y : WithTop ℤ} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      norm_cast at hx hy ⊢
      omega

theorem val_prime_eq_zero {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l) (hvl : 0 < v (l : F)) :
    v (p : F) = 0 := by
  have hI : ∀ a : ℤ, 0 ≤ v (a : F) := fun a =>
    nonneg_of_isIntegral v (by simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := a)))
  have hp0 : 0 ≤ v (p : F) := by simpa using hI p

  have hcop : IsCoprime (p : ℤ) (l : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hl).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hF : (a : F) * (p : F) + (b : F) * (l : F) = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) hab
    push_cast at this
    exact this
  by_contra hne0
  have hpos : 0 < v (p : F) := lt_of_le_of_ne hp0 (Ne.symm hne0)
  have h1 : 0 < v ((a : F) * (p : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI a) hpos
  have h2 : 0 < v ((b : F) * (l : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI b) hvl
  have h3 := lt_of_lt_of_le (lt_min h1 h2) (v.map_add _ _)
  rw [hF, AddValuation.map_one] at h3
  exact lt_irrefl _ h3

end Val

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem mem_range_of_isRoot (P : (FractionRing O)[X]) (hm : P.Monic)
    (hc : ∀ i, P.coeff i ∈ (algebraMap O (FractionRing O)).range) {μ : FractionRing O} (hμ : P.IsRoot μ) :
    μ ∈ (algebraMap O (FractionRing O)).range := by
  have hlift : P ∈ Polynomial.lifts (algebraMap O (FractionRing O)) :=
    (Polynomial.lifts_iff_coeff_lifts P).mpr (fun n => hc n)
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hm
  have hint : IsIntegral O μ := ⟨Q, hQm, by rw [← Polynomial.eval_map, hQ]; exact hμ⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy⟩

end DVR

end Formalism.L2.NCov
