import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem one_le_rk_of_not_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (L : Lev g N)
    (hL : L.sharp = false) : 1 ≤ rk ρ L.e := by
  obtain ⟨L₀, h₀, x, hx, hu⟩ := hρ
  let L' : Lev g N := { L₀ with s := L.s, k := L.k, hk := L.hk }
  have hs : L'.sharp = false := h₀
  rw [_root_.GlobalTheory.BadShare.CoDiag.rk_e_eq g N M ρ L L' (hL.trans hs.symm) rfl rfl]
  obtain ⟨a1, a2, a3, a4, -⟩ := _root_.GlobalTheory.BadShare.LevGroup.lev_group g N L'
  obtain ⟨-, -, -, h⟩ := _root_.GlobalTheory.BadShare.EpsProj.eps_spec (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4
  refine h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_
  intro i u hm
  have hchi : L'.chi u = L₀.chi u := by
    simp only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]
    rfl
  rw [hchi]
  exact hu u hm.1

theorem rk_lower_of_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (s : ℕ) :
    ∀ L : Lev g N, L.sharp = true → L.s = s → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  induction s with
  | zero => exact fun L h1 h2 => _root_.GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero g N M ρ hρ L h1 h2
  | succ s ih =>
    intro L h1 h2
    have hk : s + L.k < N := by have := L.hk; omega
    let L' : Lev g N := { L with s := s, hk := hk }
    have h3 := ih L' h1 rfl
    have h4 := _root_.GlobalTheory.BadShare.RxStep.rk_le_step g N M ρ L L' h1 h1 rfl h2
    exact h3.trans (by exact_mod_cast h4)

theorem rk_lev_lower : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  intro g _ N M _ _ _ ρ hρ L
  by_cases h : L.sharp = true
  · rw [if_pos h]
    exact rk_lower_of_sharp g N M ρ hρ L.s L h rfl
  · rw [if_neg h, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ rk ρ L.e := by
      exact_mod_cast one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)
    have h2 : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    linarith

end GlobalTheory.BadShare
