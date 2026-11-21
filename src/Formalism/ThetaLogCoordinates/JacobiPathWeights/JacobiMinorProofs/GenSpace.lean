import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.GenSpaceFacts
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace GS

section Slices

variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]

def slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ e ∈ P.support, monomial e (θ (coeff e P))

theorem coeff_slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slcFun θ P) = θ (coeff e P) := by
  classical
  simp only [slcFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    simp [h]

def slc (θ : A →ₗ[k] B) : MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := slcFun θ
  map_add' P Q := by
    ext e
    simp [coeff_slcFun]
  map_smul' c P := by
    ext e
    simp [coeff_slcFun]

@[simp] theorem coeff_slc (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slc θ P) = θ (coeff e P) := coeff_slcFun θ P e

def slMap (P : MvPolynomial σ A) : (A →ₗ[k] k) →ₗ[k] MvPolynomial σ k where
  toFun ℓ := slc ℓ P
  map_add' ℓ ℓ' := by
    ext e
    simp
  map_smul' c ℓ := by
    ext e
    simp

def slSpace (P : MvPolynomial σ A) : Submodule k (MvPolynomial σ k) := LinearMap.range (slMap (k := k) P)

theorem mem_slSpace {P : MvPolynomial σ A} {f : MvPolynomial σ k} :
    f ∈ slSpace (k := k) P ↔ ∃ ℓ : A →ₗ[k] k, slc ℓ P = f := Iff.rfl

end Slices

section Universal

variable (k : Type*) [Field k] (n : ℕ)

variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]

theorem algebraMap_gen : algebraMap k (GenField k n) = genφ k n := rfl

theorem genMat_isUnit : IsUnit (genMat k n).det := isUnit_iff_ne_zero.mpr (genMat_det_ne k n)

end Universal

end GS

open GS

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
