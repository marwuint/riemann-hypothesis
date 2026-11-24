module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
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
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma lin_coeff_sq {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, constantCoeff (φ f) = algebraMap O K (x f)) (i : τ) :
    ∀ g ∈ RingHom.ker x ^ 2, coeff (Finsupp.single i 1) (φ g) = 0 := by
  intro g hg
  rw [pow_two] at hg
  have hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order := by
    intro a ha
    have hxa : x a = 0 := ha
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])
  have hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order := by
    refine Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add (hone a ha) (hone b hb)
        _ ≤ (φ a * φ b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _)]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by norm_num) hord

theorem UpperTheory.V.Alg.chart_gr :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (τ : Type) (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ → IsChart W.gr (W.originA h) wt (φ.comp W.A.val) := by
  intro O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ
  obtain ⟨hk, hsurj⟩ := ker_pow O R X W h 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun j f hf => hφ.graded j f.val hf
  · exact fun f => hφ.const f.val
  · intro i
    obtain ⟨g, hg1, hg2⟩ := hφ.onto i
    obtain ⟨y, hy⟩ := hsurj g
    have hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0 :=
      fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy
    have he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) =
        coeff (Finsupp.single i' 1) (φ g) := by
      intro i'
      have := hd i'
      rw [map_sub, map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨y, ?_, ?_⟩
    · rwa [he]
    · intro i' hi'
      rw [he]
      exact hg2 i' hi'
  · intro f hf hco
    obtain ⟨c, hc0, hcf⟩ := hφ.inj f.val hf hco
    refine ⟨c, hc0, ?_⟩
    rwa [← hk, Ideal.mem_comap]
