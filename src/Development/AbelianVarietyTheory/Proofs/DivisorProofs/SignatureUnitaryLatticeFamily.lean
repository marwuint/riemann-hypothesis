import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NotIsSRepsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepsModKM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCount
open GlobalTheory.UCls.Model GlobalTheory.SUVol.TamModel
open scoped Pointwise nonZeroDivisors TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_small {Ψ : Finset (E →+* ℂ)}
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (α : 𝓞 E)
    (h : ∀ τ ∈ Ψ, ‖τ (α : E)‖ < 1) : α = 0 := by
  by_contra h0
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm h0
  by_cases hs : σ ∈ Ψ
  · exact absurd (h σ hs) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ Ψ := by
      by_contra h2; exact hs ((hΨ σ).2 h2)
    have h2 := h _ h1
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h2
    exact absurd h2 (not_lt.2 hσ)

def ratSU (G : Matrix (Fin r) (Fin r) E) : Subgroup (GL (Fin r) E) where
  carrier := {γ | (γ : Matrix (Fin r) (Fin r) E).det = 1 ∧
    ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {g g'} hg hg' :=
    ⟨by simp [hg.1, hg'.1], fun u w => by simp only [Units.val_mul, ← mulVec_mulVec, hg.2, hg'.2]⟩
  inv_mem' {g} hg := by
    refine ⟨?_, fun u w => ?_⟩
    · have := congrArg Matrix.det g.mul_inv
      rwa [det_mul, hg.1, one_mul, det_one] at this
    · rw [← hg.2]
      simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]

def toAd (E : Type) [Field E] [NumberField E] (r : ℕ) :
    GL (Fin r) E →* GL (Fin r) (RA (maximalRealSubfield E) E) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight :
    E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).toRingHom

end GlobalTheory.SUCount
