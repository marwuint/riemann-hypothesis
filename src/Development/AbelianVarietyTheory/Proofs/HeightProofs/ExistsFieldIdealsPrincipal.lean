import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize

end GlobalTheory.FieldSize
