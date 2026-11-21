import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.Branching

def lastNat {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨n - 1, by omega⟩ else 0

theorem natW_add_lastNat {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (a : Fin n) : lam.natW a + lastNat ν = ν a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha : a ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.2 (by have := a.2; simp only; omega)
  have hl := lam.anti ha
  rw [h, h] at hl
  simp only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]
  omega

theorem detPowMul_mem {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (v : nablaSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := by
  have hm := (genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2
  have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
  rwa [e] at hm

def detPowMul {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c) :
    nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν)).comp
    (nablaSq ℂ n lam).subtype) (detPowMul_mem ν c lam h)

theorem detPowMul_coe {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (v : nablaSq ℂ n lam) : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) =
      Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) := rfl

end GlobalTheory.Branching

namespace GlobalTheory.Branching

end GlobalTheory.Branching
