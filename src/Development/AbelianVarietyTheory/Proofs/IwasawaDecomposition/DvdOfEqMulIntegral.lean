import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayDataNonempty
import Formalism.LocalRingCardinality.ConjSqrtMinusD

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

end GlobalTheory.Mem.NormPrime
