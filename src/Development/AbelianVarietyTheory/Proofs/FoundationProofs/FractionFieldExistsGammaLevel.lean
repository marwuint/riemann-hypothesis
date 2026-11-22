import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem sl_ofSL_io_of_gamma {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) (a : ring ε.range) (M : ℕ)
    (ha : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, (a : ℍ → ℂ) (γ • τ) = (a : ℍ → ℂ) τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) : T.sl (ofSL γ) (T.io a) = T.io a := by
  apply T.sl_io
  rw [_root_.GlobalTheory.FN.cmp_props.2.2.1 γ a]
  funext τ
  exact (ha γ hγ τ).symm

theorem frac_exists_level (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K) :
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  obtain ⟨a, b, hb, hf⟩ := T.io_surj f
  obtain ⟨N₁, w₁, hN₁, h₁⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 a).1 a.2
  obtain ⟨N₂, w₂, hN₂, h₂⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 b).1 b.2
  have hM : 0 < N₁ * N₂ := Nat.mul_pos hN₁ hN₂
  have h₁' := _root_.GlobalTheory.FN.lv_mono ε.range N₁ (N₁ * N₂) w₁ w₁ a hM (dvd_mul_right _ _) le_rfl h₁
  have h₂' := _root_.GlobalTheory.FN.lv_mono ε.range N₂ (N₁ * N₂) w₂ w₂ b hM (dvd_mul_left _ _) le_rfl h₂
  refine ⟨N₁ * N₂, hM, fun γ hγ => ?_⟩
  have ea := sl_ofSL_io_of_gamma T a _ h₁'.1 γ hγ
  have eb := sl_ofSL_io_of_gamma T b _ h₂'.1 γ hγ
  have hib : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have key : T.sl (ofSL γ) f * T.io b = f * T.io b := by
    have := congrArg (T.sl (ofSL γ)) hf
    rw [map_mul, eb, ea] at this
    rw [this, hf]
  exact mul_right_cancel₀ hib key

end GlobalTheory.FN
