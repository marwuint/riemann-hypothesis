import Formalism.HermitianCurvature.LatticeHerglotzBound

open MeasureTheory Set Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.NthRootMeasurability

open Formalism.FourierDecayAlt.crystallineComparison

theorem detC (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)

def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)

def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}

theorem measurable_R (s k : ℕ) : Measurable (R s k) := by
  unfold R; fun_prop

theorem measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2

theorem R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by
  unfold R zeta
  rw [mul_pow, ← pow_mul, mul_comm k s, pow_mul, (Complex.isPrimitiveRoot_exp s hs).pow_eq_one,
    one_pow, one_mul, Complex.cpow_nat_inv_pow w hs]

theorem nthRoots_eq_R (s : ℕ) (hs : s ≠ 0) (w : ℂ) :
    nthRoots s w = (Multiset.range s).map (fun k => R s k w) :=
  (Complex.isPrimitiveRoot_exp s hs).nthRoots_eq (Complex.cpow_nat_inv_pow w hs)

theorem A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by
  intro j hj k hk hjk
  rw [Function.onFun, Set.disjoint_left]
  intro z hzj hzk
  apply hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have e : zeta s ^ j * (z ^ s) ^ ((s : ℂ)⁻¹) = zeta s ^ k * (z ^ s) ^ ((s : ℂ)⁻¹) := by
    have := hzj.2.trans hzk.2.symm
    simpa [R] using this
  have hα : (z ^ s) ^ ((s : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := hzj.2
    simp only [R, h0, mul_zero] at this
    exact hzj.1 this.symm
  exact (Complex.isPrimitiveRoot_exp s hs).pow_inj hj hk (mul_right_cancel₀ hα e)

theorem A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, A,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hz, _⟩; exact hz
  · intro hz
    have hmem : z ∈ nthRoots s (z ^ s) := (mem_nthRoots (Nat.pos_of_ne_zero hs)).mpr rfl
    rw [nthRoots_eq_R s hs, Multiset.mem_map] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    exact ⟨k, Multiset.mem_range.mp hk, hz, hkz⟩

theorem image_A (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem injOn_A (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']

end Formalism.FourierDecayAlt.P.NthRootMeasurability

