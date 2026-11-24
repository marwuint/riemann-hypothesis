module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  choose U hU using hu
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply IsFractionRing.injective (WittVector p k) (Fr p k)
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    choose F hF using hf
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    choose F hF using hf
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
