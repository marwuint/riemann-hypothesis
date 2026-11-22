import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

noncomputable section SlopeTestRemainingChoices

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Lit
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Lit.KT.EigenformSpan

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

end UpperTheory.V.Lit.KT.EigenformSpan

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

