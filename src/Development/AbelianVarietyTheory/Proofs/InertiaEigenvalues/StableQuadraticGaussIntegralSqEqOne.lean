import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussNegOneEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOne
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem stableGauss_sq_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → G₁ ^ 2 = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω hH G₁ hG
  have hG' := _root_.GlobalTheory.JR.WeilQuad.stableGauss_neg_one F E A ψ x μ ω hH G₁ hG
  obtain ⟨Λ₀, -, hc₀, h₀⟩ := hG
  obtain ⟨Λ₁, -, hc₁, h₁⟩ := hG'
  obtain ⟨Λ, ho, hc, hsub, hperp, hV⟩ := _root_.GlobalTheory.JR.WeilQuad.LargeLattice.main F E A ψ x μ ω hH ((Λ₀ : Set A.L) ∪ Λ₁) (hc₀.union hc₁)
    _ (_root_.GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero F E A ψ x μ ω hH)
  have e0 := h₀ Λ ho hc (fun y hy => hsub (Or.inl hy))
  have e1 := h₁ Λ ho hc (fun y hy => hsub (Or.inr hy))
  have hp := _root_.GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one F E A ψ x μ ω hH Λ ho hc hperp (fun y hy => hV hy)
  rw [e0, e1] at hp
  rw [sq]; exact hp

end GlobalTheory.JR.WeilQuad
