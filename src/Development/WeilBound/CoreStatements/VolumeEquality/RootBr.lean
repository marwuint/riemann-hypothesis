module

public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section

namespace SheetDecomposition

open Filter Topology Polynomial

theorem eval_monicOf {d : ℕ} (a : Fin d → ℂ) (x : ℂ) : (monicOf a).eval x = x ^ d + ∑ i, a i * x ^ (i : ℕ) := by
  simp [monicOf, eval_finsetSum]

theorem degree_low_lt {d : ℕ} (a : Fin d → ℂ) : (∑ i, C (a i) * X ^ (i : ℕ) : ℂ[X]).degree < d :=
  degree_sum_fin_lt a

theorem monic_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).Monic :=
  monic_X_pow_add (degree_low_lt a)

theorem natDegree_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).natDegree = d := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicOf
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_low_lt a

theorem root_branch {d : ℕ} (a₀ : Fin d → ℂ) (x₀ : ℂ) (h0 : (monicOf a₀).IsRoot x₀)
    (h1 : (derivative (monicOf a₀)).eval x₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, ψ a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ ψ a ∧ (monicOf a).IsRoot (ψ a) := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf
  have cdf : ContDiffAt ℂ 1 f (a₀, x₀) := by
    rw [hf]
    fun_prop
  have hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀) := by
    have e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x))
        (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀ :=
      HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)
    have e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x := by
      funext x
      simp [hf, eval_monicOf]
    rw [e2] at e1
    exact e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt
  have if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩
  have hc := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hv := cdf.eventually_apply_implicitFunction one_ne_zero if₂
  filter_upwards [hc.eventually (by simp), hv] with a ha hb
  refine ⟨ha.differentiableAt one_ne_zero, ?_⟩
  have : f (a₀, x₀) = 0 := by
    have := h0
    rwa [IsRoot.def, eval_monicOf] at this
  rw [this] at hb
  rwa [IsRoot.def, eval_monicOf]

theorem root_iff_of_injective {d : ℕ} (a : Fin d → ℂ) (r : Fin d → ℂ) (hr : Function.Injective r)
    (h : ∀ i, (monicOf a).IsRoot (r i)) (x : ℂ) : (monicOf a).IsRoot x ↔ ∃ i, x = r i := by
  classical
  refine ⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩
  by_contra hne
  push Not at hne
  have hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact h i
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
    intro hz
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
    exact hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := (Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))
  rw [natDegree_monicOf] at h2
  omega

theorem exists_roots {d : ℕ} (a : Fin d → ℂ) (hs : (monicOf a).Separable) :
    ∃ r : Fin d → ℂ, Function.Injective r ∧ ∀ i, (monicOf a).IsRoot (r i) := by
  classical
  have hc : (monicOf a).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]
  let e := Finset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
  have := (e.symm i).2
  rwa [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero] at this

theorem rootBranches : RootBranches := by
  intro n d T a hT ha hs t₀ ht₀
  obtain ⟨r, hr, hroot⟩ := exists_roots (a t₀) (hs t₀ ht₀)
  have hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0 := fun i => by
    have := (hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)
    simpa using this
  choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)
  have hca : ContinuousAt a t₀ := (ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt
  have hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀ := fun i =>
    ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧
      ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t) := by
    refine (hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have : ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0 :=
        ((hcθ i).sub (hcθ j)).eventually_ne (by
          show ψ i (a t₀) - ψ j (a t₀) ≠ 0
          rw [hψ0, hψ0]
          exact sub_ne_zero.mpr (hr.ne hij))
      filter_upwards [this] with t ht _ using sub_ne_zero.mp ht
  obtain ⟨V, hV, hVo, hVt⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩
  · exact (((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt
  · have hi : Function.Injective fun i => ψ i (a t) := fun i j h => by
      by_contra hij
      exact (hV t ht).2.2 i j hij h
    exact ⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩

end SheetDecomposition
