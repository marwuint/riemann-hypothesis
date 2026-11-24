module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem cutoff : Cutoff := by
  intro Γ V S _ _ _ _ d G W hW
  obtain ⟨hWo, hWc, hWf⟩ := hW
  choose φ hφs hφd hφr using fun s => (hWo s).1.exists_contDiff_support_eq (n := ⊤)
  have hnn : ∀ s x, 0 ≤ φ s x := fun s x => (hφr s ⟨x, rfl⟩).1
  have hne : ∀ s x, φ s x ≠ 0 ↔ x ∈ W s := fun s x => by rw [← Function.mem_support, hφs]
  let Φ : S → V → ℝ := fun s p => ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)
  have hinv : ∀ (δ : Γ) s p, Φ (G.σ δ⁻¹ s) (G.ρ δ⁻¹ p) = Φ s p := by
    intro δ s p
    simp only [Φ]
    rw [← finsum_comp_equiv (Equiv.mulLeft δ) (f := fun γ => φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))]
    refine finsum_congr fun γ => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, Equiv.Perm.mul_apply, mul_apply_eq_comp]
  have hloc : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, ∃ F : Finset Γ, ∀ x ∈ N, ∀ γ,
      φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F := by
    intro s p hp
    obtain ⟨N, hN, hNf⟩ := hWf s p hp
    exact ⟨N, hN, hNf.toFinset, fun x hx γ hγ => hNf.mem_toFinset.2 ⟨x, hx, (hne _ _).1 hγ⟩⟩
  have hΦeq : ∀ s (F : Finset Γ) x, (∀ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F) →
      Φ s x = ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) :=
    fun s F x h => finsum_eq_sum_of_support_subset _ (fun γ hγ => h γ hγ)
  have hpos : ∀ s, ∀ p ∈ G.Y, 0 < Φ s p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    rw [hΦeq s F p (hF p (mem_of_mem_nhds hN))]
    obtain ⟨γ, hγ⟩ := hWc s p hp
    have h0 : φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) ≠ 0 := (hne _ _).2 hγ
    exact Finset.sum_pos' (fun i _ => hnn _ _)
      ⟨γ, hF p (mem_of_mem_nhds hN) γ h0, lt_of_le_of_ne (hnn _ _) (Ne.symm h0)⟩
  have hsmooth : ∀ s, ∀ p ∈ G.Y, ContDiffAt ℝ ∞ (Φ s) p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    have hc : ContDiff ℝ ∞ (fun x => ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) :=
      ContDiff.sum (fun γ _ => (hφd _).comp (G.ρ γ⁻¹).contDiff)
    refine hc.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    exact hΦeq s F x (hF x hx)
  refine ⟨fun s x => φ s x / Φ s x, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩
  · intro p hp
    exact ((hφd s).contDiffAt.div (hsmooth s p hp) (hpos s p hp).ne').contDiffWithinAt
  · obtain ⟨N, hN, hNf⟩ := hWf s p hp
    refine ⟨N, hN, hNf.subset ?_⟩
    rintro γ ⟨x, hx, hne0⟩
    exact ⟨x, hx, (hne _ _).1 (fun h => hne0 (by simp only [h, zero_div]))⟩
  · simp only [hinv, div_eq_mul_inv]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (hpos s p hp).ne'

end UpperTheory.V.Lit.Dr
