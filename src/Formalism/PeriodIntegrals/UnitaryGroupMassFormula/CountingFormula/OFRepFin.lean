module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnipotentIntegralPreservesLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_sum_left (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (w : (VS D).V) : (VS D).hT (∑ a ∈ s, c a • e a) w = ∑ a ∈ s, star (c a) * (VS D).hT (e a) w := by

  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sum_right (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (v : (VS D).V) : (VS D).hT v (∑ a ∈ s, c a • e a) = ∑ a ∈ s, c a * (VS D).hT v (e a) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul]

theorem hT_swap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have h := (VS D).herm.eq x y
  rw [starRingEnd_apply] at h
  exact h.symm

theorem pW_dec (D : Formalism.BasicNotions.D7) (v : (VS D).V) :
    v = pW D v + ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a + ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
      - ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm := by
  unfold pW
  abel

theorem delta_zero {K : Type} [Field K] [StarRing K] {r : ℕ} (β Δ : Matrix (Fin r) (Fin (r + 1)) K)
    (R : Matrix (Fin (r + 1)) (Fin r) K) (hR : β * R = 1) (hΔR : Δ * R = 0)
    (hM : Δ.conjTranspose * β + β.conjTranspose * Δ = 0) : Δ = 0 := by
  have h : (Δ.conjTranspose * β + β.conjTranspose * Δ) * R = (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * R := by rw [hM]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hR, hΔR, Matrix.mul_one, Matrix.mul_zero,
    add_zero, Matrix.zero_mul] at h
  rw [← Matrix.conjTranspose_conjTranspose Δ, h, Matrix.conjTranspose_zero]

theorem finite_level_index : FinK := by
  intro D T T' F0 Λ hF Z R hR Wf Af hWf hAf
  obtain ⟨-, -, hFe, -, c, hc, hFz⟩ := hF
  have hE : ∀ x, Good D T' F0 Λ Z x → ∀ (a : Fin D.R.rS) b,
      (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro x hx a b
    have h := hx.2.1 (Fin.castSucc a) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hFe] at h
    simpa [betaZ] using h
  have hzm : ∀ x, Good D T' F0 Λ Z x → ∀ b,
      star c * (VS D).hT D.sp.zm (fr D x b) = Z (Fin.last _) b := by
    intro x hx b
    have h := hx.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hFz] at h
    rwa [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h
  have pW_sub : ∀ v v' : (VS D).V, pW D (v - v') = pW D v - pW D v' := by
    intro v v'
    simp only [pW, map_sub, sub_smul, Finset.sum_sub_distrib, sub_div]
    abel
  refine Set.Finite.of_injOn (f := fun x => (pWf D x, alM D x * R)) (t := Wf ×ˢ Af) ?_ ?_
    (hWf.prod hAf)
  · exact fun x hx => ⟨hx.2.1, hx.2.2⟩
  intro x hx x' hx' hxx'
  obtain ⟨hp, hal⟩ := Prod.mk.inj hxx'
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = alM D x - alM D x' := ⟨_, rfl⟩
  have huE : ∀ a b, (VS D).hT (D.sp.hypE a) (fr D x b - fr D x' b) = 0 := by
    intro a b
    rw [map_sub, hE x hx.1, hE x' hx'.1, sub_self]
  have huz : ∀ b, (VS D).hT D.sp.zm (fr D x b - fr D x' b) = 0 := by
    intro b
    have hsc : star c ≠ 0 := star_ne_zero.mpr hc
    have h0 : star c * ((VS D).hT D.sp.zm (fr D x b) - (VS D).hT D.sp.zm (fr D x' b)) = 0 := by
      rw [mul_sub, hzm x hx.1, hzm x' hx'.1, sub_self]
    rw [map_sub]
    exact (mul_eq_zero.mp h0).resolve_left hsc
  have huF : ∀ a b, (VS D).hT (D.sp.hypF a) (fr D x b - fr D x' b) = Δ a b := by
    intro a b
    rw [hΔ, Matrix.sub_apply, map_sub]
    rfl
  have hupW : ∀ b, pW D (fr D x b - fr D x' b) = 0 := by
    intro b
    rw [pW_sub]
    have h := congrFun hp b
    simp only [pWf] at h
    rw [h, sub_self]
  have hu : ∀ b, fr D x b - fr D x' b = ∑ a, Δ a b • D.sp.hypE a := by
    intro b
    conv_lhs => rw [pW_dec D (fr D x b - fr D x' b)]
    simp only [hupW, huE, huz, huF, zero_smul, Finset.sum_const_zero, zero_div, zero_add, add_zero,
      sub_zero]
  have hΔR : Δ * R = 0 := by
    rw [hΔ, Matrix.sub_mul, hal, sub_self]
  have hM : Δ.conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * Δ = 0 := by
    ext a b
    have hG : (VS D).hT (fr D x a) (fr D x b) = (VS D).hT (fr D x' a) (fr D x' b) := by
      rw [hx.1.2.2 a b, hx'.1.2.2 a b]
    have hxa : fr D x a = fr D x' a + ∑ c, Δ c a • D.sp.hypE c := by
      rw [← hu a]
      abel
    have hxb : fr D x b = fr D x' b + ∑ c, Δ c b • D.sp.hypE c := by
      rw [← hu b]
      abel
    rw [hxa, hxb] at hG
    simp only [map_add (f := _), LinearMap.add_apply] at hG
    have h1 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (∑ c, Δ c b • D.sp.hypE c) = 0 := by
      rw [hT_sum_left]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hT_sum_right]
      simp [D.sp.hyp_ee]
    have h2 : (VS D).hT (fr D x' a) (∑ c, Δ c b • D.sp.hypE c) =
        ((betaZ D Z).conjTranspose * Δ) a b := by
      rw [hT_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, ← hE x' hx'.1 c a, hT_swap D (D.sp.hypE c) (fr D x' a)]
      ring
    have h3 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (fr D x' b) = (Δ.conjTranspose * betaZ D Z) a b := by
      rw [hT_sum_left, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, hE x' hx'.1 c b]
    rw [Matrix.add_apply, Matrix.zero_apply, ← h2, ← h3]
    rw [h1, add_zero] at hG
    linear_combination hG
  have hΔ0 : Δ = 0 := delta_zero (betaZ D Z) Δ R hR hΔR hM
  have hfr : ∀ b, fr D x b = fr D x' b := by
    intro b
    have h := hu b
    rw [hΔ0] at h
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero] at h
    exact sub_eq_zero.mp h
  refine Prod.ext (funext fun i => ?_) ?_
  · simpa [fr] using hfr (Fin.castSucc i)
  · simpa [fr] using hfr (Fin.last _)

end PI.UnitaryGroupMassFormula.CntFormula
