import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]

end TupApx

end GlobalTheory.GO
