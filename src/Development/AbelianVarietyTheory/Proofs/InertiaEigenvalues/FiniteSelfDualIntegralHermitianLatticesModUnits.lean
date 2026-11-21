import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntUnitOfMulLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullClasses

theorem exists_unit_mulLat_mem_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S :=
  fun K B hsep x _ _ c hc0 =>
    finite_mod_T_of K B (_root_.GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure K B hsep) (_root_.GlobalTheory.NormUnits.exists_finset_normUnits K B hsep) (GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B) x c hc0

end GlobalTheory.HullClasses
