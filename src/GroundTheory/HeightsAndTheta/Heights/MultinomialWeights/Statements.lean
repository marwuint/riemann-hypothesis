import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

structure IndexData where
  f : ℕ
  N : ℕ
  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N

namespace IndexData

variable (d : IndexData)

def D : ℕ := RestTerms.topDegree d.f d.N

end IndexData

variable (d : IndexData)

abbrev Idx := Fin d.f × Fin d.N

abbrev XPoly := RestTerms.RootRing d.f d.N

def flagIntegralLin (f N : ℕ) : RestTerms.RootRing f N →ₗ[ℚ] ℚ where
  toFun := RestTerms.flagIntegral f N
  map_add' := RestTerms.Flag.flagIntegral_add f N
  map_smul' c Φ := by
    rw [← C_mul', RestTerms.Flag.flagIntegral_C_mul, RingHom.id_apply, smul_eq_mul]

def flagNormalisation (f N : ℕ) : ℚ :=
  (-1) ^ RestTerms.topDegree f N / (∏ i : Fin N, ((i : ℕ).factorial : ℚ)) ^ f

def intFl : XPoly d →ₗ[ℚ] ℚ := flagNormalisation d.f d.N • flagIntegralLin d.f d.N

abbrev d1 : IndexData := ⟨1, 2, 1, le_rfl, le_rfl, by norm_num⟩

end GroundTheory.Heights₂.Heights.TheoremB
