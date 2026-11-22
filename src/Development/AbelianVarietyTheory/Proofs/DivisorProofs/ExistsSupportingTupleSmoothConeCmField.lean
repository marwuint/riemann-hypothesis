import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionalPosOnSquaresEqSumOfSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmIntegralAveragingTraceTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedForms

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc NumberField

namespace GlobalTheory.Poinc

theorem exists_supports_cm : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X]
    [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X]
    [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X →
    ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  intro E _ _ _ H φ X _ _ _ _ hP r γ hγ
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  haveI : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨n, c, b, T, hc, hT, hbal, hsum0, hTpos⟩ := _root_.GlobalTheory.exists_cm_trace_tensor E H
  obtain ⟨P, hPbal, hPc, hPsq⟩ := _root_.GlobalTheory.Poinc.exists_avg_proj_balForms (𝓞 E) H.bar X n c b T hc hT hbal hsum0 hTpos
  have hpos : ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < (ℓ ∘ₗ P) (sqForm l) := by
    intro l hl
    obtain ⟨hne, hpsd⟩ := hPsq l hl
    have hb := hPbal (sqForm l) fun x y => by simp [mul_comm]
    have h4 := hP.pos _ hb hpsd hne
    have h5 := h2 _ hb hpsd
    have h6 : (0 : ℝ) < ℓ (P (sqForm l)) := lt_of_lt_of_le (by positivity) h5
    exact_mod_cast h6
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := _root_.GlobalTheory.Poinc.SumSqFunctional.sumsq_functional X (ℓ ∘ₗ P) hpos
  have key : ∀ β ∈ balForms H.bar X, ∑ i, β (a i) (a i) = ((D * c : ℕ) : ℤ) * ℓ β := by
    intro β hβ
    rw [hsum β hβ.1, LinearMap.comp_apply, hPc β hβ, map_zsmul, smul_eq_mul]
    push_cast; ring
  have hDc : (0 : ℝ) < ((D * c : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hD hc
  refine ⟨N * (D * c), m, a, Nat.mul_pos hN (Nat.mul_pos hD hc),
    ⟨hspan, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩⟩
  · rw [key β hβ]
    have := h2 β hβ hp
    push_cast at this hDc ⊢
    nlinarith
  · rw [key _ (hγ.mem j)]
    push_cast
    rw [h1 j]; ring
  · rw [key β hβ] at he
    refine h3 β hβ hp ?_
    push_cast at he hDc
    have : ((D : ℝ) * c) * (N * φ.evalZ β) = ((D : ℝ) * c) * ℓ β := by rw [← he]; ring
    exact mul_left_cancel₀ hDc.ne' this

end GlobalTheory.Poinc
