import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeGalois

theorem gram_ge {K K' V V' ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) =
      1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) := fun x => by
    have h := ht w.embedding (∑ k, x k • e k)
    rw [← (hG' w).2, map_sum] at h
    simp only [map_smulₛₗ] at h
    rw [normAt_sum] at h
    rw [one_mul]
    exact h.symm
  rw [hv, gramPl_eq, gramPl_eq]
  refine le_of_le_of_eq ?_ (by rw [one_pow, one_mul] : (1 : ℝ) ^ (2 * j) * _ = _)
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine (this.trans ?_).symm
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]

end GlobalTheory.SlopeGalois
