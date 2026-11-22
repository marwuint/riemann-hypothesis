import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators
open Module

namespace PI.KerIso.FourSqW

section Conj

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : K := Classical.choose (hc.2.1 k)

theorem conjFun_spec (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    algebraMap K E (conjFun cj hc k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (hc.2.1 k)).symm

theorem conjFun_conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    conjFun cj hc (conjFun cj hc k) = k :=
  (algebraMap K E).injective (by rw [conjFun_spec, conjFun_spec, hc.1])

def conjK (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) : K ≃+* K where
  toFun := conjFun cj hc
  invFun := conjFun cj hc
  left_inv := conjFun_conjFun cj hc
  right_inv := conjFun_conjFun cj hc
  map_mul' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_mul, map_mul, map_mul, conjFun_spec, conjFun_spec])
  map_add' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_add, map_add, map_add, conjFun_spec, conjFun_spec])

end Conj

section Orth

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def trL (cj : E ≃ₐ[ℚ] E) (y : E) : E →ₗ[K] K :=
  (Algebra.trace K E).comp (LinearMap.mulRight K (cj y))

theorem trL_apply (cj : E ≃ₐ[ℚ] E) (y x : E) : trL (K := K) cj y x = Algebra.trace K E (x * cj y) := rfl

end Orth

end PI.KerIso.FourSqW
