import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

end GlobalTheory.IdxAll
