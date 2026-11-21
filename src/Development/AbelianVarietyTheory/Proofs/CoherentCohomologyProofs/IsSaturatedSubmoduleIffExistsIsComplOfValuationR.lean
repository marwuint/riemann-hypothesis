import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply

open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

end General

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in

theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing R (M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing R N

end Valuation

universe u

end GlobalTheory
