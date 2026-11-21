import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem span_fibreVec_eq_top (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) = ⊤ := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have := finite_quotient_span hs hcard
  set m := Nat.card (E ⧸ N)
  have hm : 0 < m := Nat.card_pos
  have hmem : ∀ e : E, m • e ∈ N := fun e ↦
    (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul]; exact card_nsmul_eq_zero')
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have h1 : ∀ e ∈ N, fibreVec h σ e ∈ W := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp [fibreVec]
    | add x y _ _ hx hy => rw [fibreVec_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [fibreVec_smul]; exact W.smul_mem _ hx
  have h2 : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have := h1 _ (hmem e)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K) m e, fibreVec_smul] at this
    have hc : (σ ((m : 𝓞 K) : K)) = (m : ℂ) := by simp
    rw [hc] at this
    exact (W.smul_mem_iff (Nat.cast_ne_zero.mpr hm.ne')).mp this
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective x
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | add y z hy hz => rw [map_add]; exact W.add_mem hy hz
  | tmul z e =>
    have hz : (z ⊗ₜ[𝓞 K] e : Fibre σ E) = ((ofComplex σ).symm z) • ((1 : ComplexAt σ) ⊗ₜ e) := by
      rw [← fibre_smul_eq, smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul]
    exact W.smul_mem _ (h2 e)

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
