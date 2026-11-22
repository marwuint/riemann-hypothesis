import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem restrLen_of_irrelevant (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl

end Lemmas

end GroundTheory.Heights₂.Heights.Kleiman
