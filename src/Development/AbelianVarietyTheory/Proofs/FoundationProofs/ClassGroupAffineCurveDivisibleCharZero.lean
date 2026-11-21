import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne

open Polynomial

namespace GlobalTheory

theorem classGroup_ringOfIntegers_divisible : GlobalTheory.NeedB.ClDiv := by
  intro k K _ _ _ _ _ _ _ _ N hN c
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    exact ⟨c, (pow_one c).symm⟩
  set A := FunctionField.ringOfIntegers k K
  have : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  have : Module.Free k[X] A := IsIntegralClosure.module_free k[X] (RatFunc k) K _
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) K _
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  letI : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.exists_integral_norm_natDegree_mod_eq_one k K N hN
  have hdim : Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hf0]
    exact hf
  exact _root_.GlobalTheory.classGroup_nthPower_of_codim_one_mod k A N hN (_root_.GlobalTheory.exists_class_group_mk0_eq_mul_pow k A N h) ⟨f, hf0, hdim⟩ c

end GlobalTheory
