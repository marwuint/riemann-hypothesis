import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem charZero_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun m hm => ?_
  have hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (m : ℤ)) = 0
    simp only [mConeMap, eq_intCast, Int.cast_natCast]
    rw [map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]
  rw [hV.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem isHomogeneous_of_map {σ : Type} {F : MvPolynomial σ ℤ} {m : ℕ}
    (h : (map (Int.castRingHom ℚ) F).IsHomogeneous m) : F.IsHomogeneous m := fun {d} hd =>
  h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)

theorem norm_prod_le_pow {B : ℝ} (hB : 0 ≤ B) (m : Multiset ℂ) (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hB

theorem norm_last_le {n : ℕ} (a : ℕ → ℂ) (ha : a 0 = 1) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), a i * w ^ (n - i) = 0 → ‖w‖ ≤ B) :
    ‖a n‖ ≤ B ^ n := by
  classical
  set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp
  have hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0 := by
    intro k
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hdeg : p.natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hlead : p.coeff n = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [ha]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hmon : p.Monic := Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)
  have hzero : p.coeff 0 = a n := by
    rw [hcoeff, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = n := by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]
  have hprod := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
  rw [hzero, hnat] at hprod
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]
  refine norm_prod_le_pow hB _ fun w hw => hroot w ?_
  have hw' := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rw [Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum] at hw'
  simpa using hw'

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
