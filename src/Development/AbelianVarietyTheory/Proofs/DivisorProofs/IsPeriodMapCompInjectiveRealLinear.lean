module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PELU

theorem isPeriod_comp_realLinear {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (hP₀ : IsPeriod D ρ P₀) (hR : Function.Injective R)
    (hRρ : ∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (hE : ∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) :
    IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP₀
  have hsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hR
  let e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo R hR
  have he : ∀ z, e z = R z := fun z => rfl
  let ec := e.toContinuousLinearEquiv
  refine ⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩
  · intro a x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]
  · exact hR.comp h2
  · let f : (R.toAddMonoidHom.comp P₀).range → P₀.range := fun z =>
      ⟨ec.symm z.1, by
        obtain ⟨z, x, rfl⟩ := z
        exact ⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ec.symm.continuous.comp continuous_subtype_val
    have hi : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have := congrArg (fun u : P₀.range => ec u.1) h
      simpa [f] using this
    exact DiscreteTopology.of_continuous_injective hf hi
  · have : Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀ := by
      rw [← Set.range_comp]; rfl
    rwa [this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]
  · exact fun x y => hE x y

end GlobalTheory.PELU
