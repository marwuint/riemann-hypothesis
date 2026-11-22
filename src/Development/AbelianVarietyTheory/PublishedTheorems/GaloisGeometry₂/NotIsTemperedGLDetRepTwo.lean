import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

namespace GlobalTheory.LocGL.TemperedTests

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GenericUnitary Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL k) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocGL.TemperedTests

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GKCoh.Tests

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem dchi_absC_one (s : ℂ) : dchi (Model.absC E s) 1 = s * (2 * Fintype.card (InfinitePlace E)) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A, mul_comm]

theorem prod_coord {M : Type} [CommMonoid M] (F : ℂ → M) (z : Cinf E) :
    ∏ τ : E →+* ℂ, F (coord τ z) = ∏ w, F (z w) * F (starRingEnd ℂ (z w)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have e : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← h]; ext x; simp)
    · rintro (rfl | rfl) <;> simp
  rw [e, Finset.prod_pair hne]
  simp [coord, hne]

theorem dchi_absC (s : ℂ) (z : Cinf E) : dchi (Model.absC E s) z = s * ∑ w, (2 * ((z w).re : ℝ) : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ := s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  rw [h]
  simp [A]

end GlobalTheory.GKCoh.Tests
