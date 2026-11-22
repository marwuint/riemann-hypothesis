import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatTrace

open Polynomial

theorem aeval_mulVec_of_eigen {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : Type*}
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (hv : Q *ᵥ v = μ • v) (p : R[X]) :
    (aeval Q p) *ᵥ v = (aeval μ p) • v := by
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]

theorem aeval_restrict_coe {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (L : Submodule ℤ (n → S))
    (hQ : ∀ x ∈ L, (Q.mulVecLin.restrictScalars ℤ) x ∈ L) (p : ℤ[X]) (x : L) :
    ((aeval (LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ) p x : L) : n → S) =
      (aeval Q p) *ᵥ (x : n → S) := by
  set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ
  have hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ',
        ← Matrix.mulVec_mulVec, ← ih]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq,
      Matrix.add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

theorem isIntegral_trace_of_isIntegral {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨p, hpm, hp0⟩ := hM
  have hpM : aeval M p = 0 := by rw [aeval_def]; exact hp0
  set M' := M.map φ
  have hpM' : aeval M' p = 0 := by
    have h := Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hpM, map_zero] at h
    exact h
  have htr : φ M.trace = M'.trace := by
    simp [Matrix.trace, M', map_sum]
  have hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have h0 : M'.charpoly.eval μ = 0 := (Polynomial.mem_roots'.1 hμ).2
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hev : M' *ᵥ v = μ • v := by
      have h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v := by
        rw [Matrix.sub_mulVec]
        congr 1
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [h1, sub_eq_zero] at hv
      exact hv.symm
    have h2 := aeval_mulVec_of_eigen M' μ v hev p
    rw [hpM', Matrix.zero_mulVec] at h2
    have hz : aeval μ p = 0 := by
      by_contra hne
      exact hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)
    exact ⟨p, hpm, by rw [← aeval_def]; exact hz⟩
  have hsum : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    have := multiset_sum_mem (M'.charpoly.roots)
      (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))
    exact (mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this
  rw [← htr] at hsum
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum

end GlobalTheory.LatTrace

end
