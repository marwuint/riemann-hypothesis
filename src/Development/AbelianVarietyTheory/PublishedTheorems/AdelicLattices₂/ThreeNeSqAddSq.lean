import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.Published.LandherrModel

abbrev Qi : Type := CyclotomicField 4 ℚ

instance cyclo : IsCyclotomicExtension {4} ℚ Qi := by
  have h : @IsCyclotomicExtension {4} ℚ Qi _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance cm : IsCMField Qi := IsCyclotomicExtension.Rat.isCMField Qi (S := {4}) ⟨4, rfl, by norm_num⟩

noncomputable def ii : Qi := IsCyclotomicExtension.zeta 4 ℚ Qi

theorem ii_mul : ii * ii = -1 := by
  have h := IsCyclotomicExtension.zeta_spec 4 ℚ Qi
  have := (h.pow (a := 2) (b := 2) (by norm_num) (by norm_num)).eq_neg_one_of_two_right
  rw [← this, pow_two]; rfl

theorem cc_ii : IsCMField.complexConj Qi ii = -ii := by
  let τ : Qi →+* ℂ := Classical.choice inferInstance
  apply τ.injective
  have h : τ ii * τ ii = -1 := by rw [← map_mul, ii_mul]; simp
  have h' : τ ii = Complex.I ∨ τ ii = -Complex.I := by
    rw [← mul_self_eq_mul_self_iff, h]; simp
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  rcases h' with h' | h' <;> simp [h']

noncomputable def A : Matrix (Fin 2) (Fin 2) Qi := !![1, ii; -ii, 3]

theorem exists_coord (x : Qi) : ∃ a b : ℚ, x = a + b * ii := by
  have hli : LinearIndependent ℚ ![(1 : Qi), ii] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : Qi) + (t : Qi) * ii = 0 := by
      simpa [Algebra.smul_def] using hst
    have h2 : ((s ^ 2 + t ^ 2 : ℚ) : Qi) = 0 := by
      push_cast
      linear_combination ((s : Qi) - t * ii) * h1 + (t : Qi) ^ 2 * ii_mul
    have h3 : s ^ 2 + t ^ 2 = 0 := by exact_mod_cast h2
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg t]
  have hr : Module.finrank ℚ Qi = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) Qi
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hr]; simp)
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x, Fin.sum_univ_two]
  simp [b, Algebra.smul_def]

end GlobalTheory.Published.LandherrModel
