import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQ
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem coeff_fg : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω),
    InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε f h hf hh
  obtain ⟨N, w, hN, hLv⟩ := hf
  obtain ⟨b, hb, hbE⟩ := hLv.2 1
  have hb' : HasQ N (fun τ => DD τ ^ w * f τ) b := by
    simpa only [one_smul] using hb
  choose a ha using fun n => (hbE n : b n ∈ ε.range)
  have hb'' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) := by
    have : (fun n => ε (a n)) = b := funext ha
    rw [this]; exact hb'
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.FN.qcoeff_finitelyGenerated Ω ε N w f a hN hLv hb''
  obtain ⟨H, hH, hHa, hH0⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε N (fun τ => DD τ ^ w * f τ) a hN hb''
  obtain ⟨hD, hDe, hD0, hDl, hDz⟩ := _root_.GlobalTheory.FNExpD.expD Ω ε
  obtain ⟨hops, huniq, hC, -, -⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  obtain ⟨hmul, hinv⟩ := _root_.GlobalTheory.HahnSub.coeff_mul_inv_mem Ω (Subring.closure (S : Set Ω))
  set A := Subring.closure (S : Set Ω)

  have hpow : ∀ k : ℕ, IsExp ε (fun τ => DD τ ^ k) (hD ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hC 1
      simpa [map_one] using this
    | succ k ih =>
      have e : (fun τ => DD τ ^ (k + 1)) = (fun τ => DD τ ^ k) * DD := by
        funext τ; simp [pow_succ]
      rw [e, pow_succ]
      exact (hops _ _ _ _ ih hDe).2.2
  have hprod : IsExp ε (fun τ => DD τ ^ w * f τ) (hD ^ w * h) := (hops _ _ _ _ (hpow w) hh).2.2
  have hEq : hD ^ w * h = H := huniq _ _ _ hprod hH
  have hDw0 : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hEq' : h = H * (hD⁻¹) ^ w := by
    rw [← hEq, inv_pow, mul_comm (hD ^ w) h, mul_assoc, mul_inv_cancel₀ hDw0, mul_one]

  have hHA : ∀ r, H.coeff r ∈ A := by
    intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hHa k]; exact hS k
    · push_neg at hr
      rw [hH0 r hr]; exact A.zero_mem
  have hDA : ∀ r, hD.coeff r ∈ A := by
    intro r
    obtain ⟨n, hn⟩ := hDz r
    rw [hn]; exact intCast_mem A n
  have hDiA : ∀ r, (hD⁻¹).coeff r ∈ A := hinv hD hDA (by rw [hDl, inv_one]; exact A.one_mem)
  have hpA : ∀ k : ℕ, ∀ r, ((hD⁻¹) ^ k).coeff r ∈ A := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero]
      by_cases hr : r = 0
      · subst hr; simpa using A.one_mem
      · simpa [hr] using A.zero_mem
    | succ k ih =>
      intro r
      rw [pow_succ]
      exact hmul _ _ ih hDiA r
  refine ⟨S, fun r => ?_⟩
  rw [hEq']
  exact hmul _ _ hHA (hpA w) r

end GlobalTheory.FN
