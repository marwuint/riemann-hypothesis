import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add, map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add, map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
