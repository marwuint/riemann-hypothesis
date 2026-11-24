module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.occursIff
    (K : Type) [Field K] [NumberField K] (n : ℕ)
    (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) (σ : SmIrr (Gw n w)) :
    Occurs μ V w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = Dp.locOn hV w g (f x) := by
  constructor
  · rintro ⟨f, hf0, hfV, hf⟩
    refine ⟨f.codRestrict V hfV, ?_, ?_⟩
    · exact fun h => hf0 (LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun h x))
    · intro g x
      apply Subtype.ext
      change f (σ.ρ g x) = Dp.localRepresentationL2 μ w g (f x)
      rw [← Dp.rhoLoc K n μ w g (f x)]
      exact hf g x
  · rintro ⟨f, hf0, hf⟩
    refine ⟨V.subtype ∘ₗ f, ?_, fun x => (f x).2, ?_⟩
    · exact fun h => hf0 (LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x))
    · intro g x
      change (f (σ.ρ g x) : LL μ) = rhoL μ w g (f x)
      rw [Dp.rhoLoc K n μ w g]
      exact congrArg Subtype.val (hf g x)
