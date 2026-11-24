module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private lemma fib_cons {m : ℕ} (a : G) (y : Fin m → G) (x : G) :
    fib (Fin.cons (α := fun _ => G) a y) x = Fin.cons (α := fun _ => G) a (fib y (a⁻¹ * x)) := by
  unfold fib
  rw [← Fin.cons_snoc_eq_snoc_cons]
  congr 2
  simp [List.ofFn_succ, mul_assoc]

private lemma continuous_fib {m : ℕ} (x : G) : Continuous fun y : Fin m → G => fib y x := by
  have hp : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply i
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact (hp.inv).mul continuous_const
  · simp only [fib, Fin.snoc_castSucc]
    exact continuous_apply j

private lemma integrable_fib (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hc : ∀ i, Continuous (φ i)) (hs : ∀ i, HasCompactSupport (φ i)) (x : G) :
    Integrable (fun y : Fin m → G => ∏ i, φ i (fib y x i)) (Measure.pi fun _ => μ) := by
  have hcont : Continuous fun y : Fin m → G => ∏ i, φ i (fib y x i) :=
    continuous_finsetProd _ fun i _ =>
      (hc i).comp ((continuous_apply i).comp (continuous_fib x))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    (K := Set.pi Set.univ fun i : Fin m => tsupport (φ i.castSucc))
    (isCompact_univ_pi fun i => hs _) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i.castSucc) ?_
  simpa only [fib, Fin.snoc_castSucc] using image_eq_zero_of_notMem_tsupport hi

private lemma push_tens (μ : Measure G) [μ.IsHaarMeasure] : ∀ (m : ℕ) (φ : Fin (m + 1) → G → ℂ),
    (∀ i, Continuous (φ i)) → (∀ i, HasCompactSupport (φ i)) →
    push μ m (fun g => ∏ i, φ i (g i)) = cvAll μ m φ := by
  intro m
  induction m with
  | zero =>
    intro φ _ _
    funext x
    simp [push, cvAll, fib, Measure.real, Measure.pi_empty_univ, Fin.snoc]
  | succ m ih =>
    intro φ hc hs
    funext x
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hint := integrable_fib μ (m + 1) φ hc hs x
    set F : (Fin (m + 1) → G) → ℂ := fun y => ∏ i, φ i (fib y x i) with hF
    have hsymm := hmp.symm
    have hint' : Integrable (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm)
        (μ.prod (Measure.pi fun _ => μ)) :=
      (hsymm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
    have hval : ∀ (a : G) (y : Fin m → G),
        (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm) (a, y) =
          φ 0 a * ∏ i, Fin.tail φ i (fib y (a⁻¹ * x) i) := by
      intro a y
      have : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm (a, y) =
          Fin.cons (α := fun _ => G) a y := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
      simp only [Function.comp, this, hF, fib_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    show ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    refine (hsymm.integral_comp' F).symm.trans ((integral_prod _ hint').trans ?_)
    simp only [cvAll, cv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hval, integral_const_mul]
    have := congrFun (ih (Fin.tail φ) (fun i => hc _) (fun i => hs _)) (a⁻¹ * x)
    rw [← this]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.pushTens :
    UpperTheory.ConvolutionTheory.L1.PushTens := by
  intro G _ _ _ _ _ _ _ _ μ _ m φ hc hs
  exact UpperTheory.ConvolutionTheory.L1.push_tens μ m φ hc hs
