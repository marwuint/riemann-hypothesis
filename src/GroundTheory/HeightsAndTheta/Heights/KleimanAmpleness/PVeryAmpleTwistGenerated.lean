import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem exists_mul_eq_prod_pow {J : Finset (Fin (N + 1))} {s : Poly k N} (hs : s ∈ monos J) :
    ∃ (t : Poly k N) (m d : ℕ), t.IsHomogeneous d ∧ s * t = (∏ i ∈ J, X i) ^ m := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨∏ i' ∈ J.erase i, X i', 1, ∑ _i' ∈ J.erase i, 1,
      IsHomogeneous.prod _ _ _ fun i' _ => isHomogeneous_X k i', ?_⟩
    rw [pow_one, Finset.mul_prod_erase J (fun i' => (X i' : Poly k N)) (Finset.mem_coe.mp hi)]
  | one => exact ⟨1, 0, 0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t₁, m₁, d₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, m₂, d₂, ht₂, h₂⟩ := hb
    exact ⟨t₁ * t₂, m₁ + m₂, d₁ + d₂, ht₁.mul ht₂, by rw [pow_add, ← h₁, ← h₂]; ring⟩

theorem exists_mem_chartRing_mul_pow (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by
  classical
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨t, m, d, ht, hst⟩ := exists_mul_eq_prod_pow (k := k) hs
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hJ0 : xProd J ≠ 0 := xProd_ne_zero J
  have hI0 : xProd I ≠ 0 := xProd_ne_zero I
  have hevJ : aeval x (∏ i ∈ J.1, (X i : Poly k N)) = xProd J := by simp [xProd, map_prod]
  have hevI : aeval x (∏ i ∈ I.1, (X i : Poly k N)) = xProd I := by simp [xProd, map_prod]
  have hst' : aeval x s * aeval x t = xProd J ^ m := by rw [← map_mul, hst, map_pow, hevJ]
  have ht0 : aeval x t ≠ 0 := right_ne_zero_of_mul (hst' ▸ pow_ne_zero m hJ0)
  have hpJ : (∏ i ∈ J.1, (X i : Poly k N)).IsHomogeneous J.1.card := by
    simpa using IsHomogeneous.prod J.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hpI : (∏ i ∈ I.1, (X i : Poly k N)).IsHomogeneous I.1.card := by
    simpa using IsHomogeneous.prod I.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hdeg : e + d = J.1.card * m := by
    have h2 : (s * t).IsHomogeneous (J.1.card * m) := by rw [hst]; exact hpJ.pow m
    have hne : s * t ≠ 0 := by
      rw [hst]
      exact pow_ne_zero _ fun h0 => hJ0 (by rw [← hevJ, h0, map_zero])
    exact (hse.mul ht).inj_right h2 hne
  obtain ⟨i', hi'⟩ : ∃ i', I.1.card = i' + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  refine ⟨aeval x (f * t * (∏ i ∈ J.1, X i) ^ (m * i')) /
      aeval x ((∏ i ∈ I.1, X i) ^ (m * J.1.card)), m,
    ⟨f * t * (∏ i ∈ J.1, X i) ^ (m * i'), (∏ i ∈ I.1, X i) ^ (m * J.1.card),
      I.1.card * (m * J.1.card),
      pow_mem (Submonoid.prod_mem _ fun i hi => X_mem_monos hi) _, ?_, hpI.pow _, rfl⟩, ?_⟩
  · have h3 := (hf.mul ht).mul (hpJ.pow (m * i'))
    convert h3 using 1
    rw [hdeg, hi']
    ring
  · have key : aeval x f / aeval x s = aeval x f * aeval x t / xProd J ^ m := by
      rw [← hst', mul_div_mul_right _ _ ht0]
    rw [key]
    simp only [map_mul, map_pow, hevJ, hevI]
    rw [hi', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero _ hJ0) (mul_ne_zero (pow_ne_zero _ hI0) (pow_ne_zero _ hJ0))]
    ring

theorem ampleChart_mul {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z₁ z₂ : Ω}
    (h₁ : z₁ ∈ ampleChart H m hh I) (h₂ : z₂ ∈ ampleChart H m hh I) :
    z₁ * z₂ ∈ ampleChart H m hh I := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  refine ⟨n₁ + n₂, ?_⟩
  rw [SubSystem.pow_sub_eq_pow] at hn₁ hn₂ ⊢
  rw [mul_add, pow_add]
  have h3 := Submodule.mul_mem_mul hn₁ hn₂
  convert h3 using 1
  ring

theorem mem_ampleChart_of_mem_chartRing {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I :=
  ⟨0, by
    rw [pow_zero, mul_one, mul_zero, SubSystem.pow_sub_eq_pow, pow_zero]
    exact Submodule.mem_one.mpr ⟨⟨c, hc⟩, rfl⟩⟩

theorem ampleChart_pow {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by
  induction n with
  | zero => rw [pow_zero]; exact mem_ampleChart_of_mem_chartRing (one_mem _)
  | succ n ih => rw [pow_succ]; exact ampleChart_mul ih hz

theorem exists_pow_mul_mem_ampleRing {L : SubSystem k x Ω} {hl b c : Ω} {J : Chart x}
    (hb : b ∈ ampleRing L 1 hl)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart L 1 hl I)
    (hc : c ∈ chartRing k x J) : ∃ E : ℕ, b ^ E * c ∈ ampleRing L 1 hl := by
  classical
  have hI : ∀ I : Chart x, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → b ^ E * c ∈ ampleChart L 1 hl I := by
    intro I
    obtain ⟨e, he⟩ := hbJ I
    obtain ⟨c', m, hc', hcc⟩ := exists_mem_chartRing_mul_pow I J hc
    have hbI : b ∈ ampleChart L 1 hl I := Set.mem_iInter.mp hb I
    refine ⟨e * m, fun E hE => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hE
    have h4 : b ^ (e * m + d) * c =
        b ^ d * (c' * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ m) := by
      rw [hcc]; ring
    rw [h4]
    exact ampleChart_mul (ampleChart_pow hbI d)
      (ampleChart_mul (mem_ampleChart_of_mem_chartRing hc') (ampleChart_pow he m))
  choose E₀ hE₀ using hI
  exact ⟨∑ I, E₀ I, Set.mem_iInter.mpr fun I =>
    hE₀ I _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I))⟩

variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
