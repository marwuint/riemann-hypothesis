import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois

open Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Orbits

lemma prim_bound {E K : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E] [FiniteDimensional E K] (g : ℕ) (hg : g.Prime)
    (μ : K) (hμ : IsPrimitiveRoot μ g) :
    g - 1 ≤ Module.finrank ℚ E * Module.finrank E K := by
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : CharZero K := by
    first
    | exact algebraRat.charZero K
    | exact (algebraMap ℚ K).charZero
  rw [Module.finrank_mul_finrank ℚ E K]
  have hint : IsIntegral ℚ μ := .of_finite ℚ μ
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1 := by
    haveI : NeZero g := ⟨hg.ne_zero⟩
    have hroot : aeval μ (cyclotomic g ℚ) = 0 := by
      rw [aeval_def, ← eval_map, map_cyclotomic]
      exact (isRoot_cyclotomic_iff.mpr hμ)
    rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ),
      natDegree_cyclotomic, Nat.totient_prime hg]
  rw [← h1, ← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

lemma dim_bound {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ Module.finrank ℚ E * k := by
  classical
  haveI := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hm0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hmk : (minpoly E M).natDegree ≤ k := by
    have h1 : minpoly E M ∣ M.charpoly := minpoly.dvd E M (Matrix.aeval_self_charpoly M)
    have h2 := natDegree_le_of_dvd h1 M.charpoly_monic.ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hfac : (X ^ g - 1 : E[X]) = (X - 1) * cyclotomic g E := by
    rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
  have hdvd : minpoly E M ∣ (X - 1) * cyclotomic g E := by
    rw [← hfac]
    apply minpoly.dvd
    simp [hM]
  have hnd : ¬ minpoly E M ∣ X - 1 := by
    rintro ⟨q, hq⟩
    apply hne
    have h0 : aeval M (X - 1 : E[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  obtain ⟨f, hf, hfm, hfΦ⟩ : ∃ f : E[X], Irreducible f ∧ f ∣ minpoly E M ∧ f ∣ cyclotomic g E := by
    by_contra hcon
    push_neg at hcon
    have hcop : IsCoprime (minpoly E M) (cyclotomic g E) :=
      isCoprime_of_irreducible_dvd (fun h => hm0 h.1) (fun z hz hzm hzΦ => hcon z hz hzm hzΦ)
    exact hnd (hcop.dvd_of_dvd_mul_right hdvd)
  have hfk : f.natDegree ≤ k := (natDegree_le_of_dvd hfm hm0).trans hmk
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  haveI : FiniteDimensional E (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hrank : Module.finrank E (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
  haveI : CharZero (AdjoinRoot f) := by
    first
    | exact algebraRat.charZero (AdjoinRoot f)
    | exact (algebraMap ℚ (AdjoinRoot f)).charZero
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have hμ : IsPrimitiveRoot (AdjoinRoot.root f) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot f)), IsRoot, eval_map]
    obtain ⟨q, hq⟩ := hfΦ
    rw [hq, eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]
  have hb := prim_bound (E := E) (K := AdjoinRoot f) g hg _ hμ
  rw [hrank] at hb
  exact hb.trans (Nat.mul_le_mul_left _ hfk)

end Orbits

open Orbits

end Formalism.FrobeniusOrbits
