import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.ExponentWindows

open Module

section Lattice

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {r : ℕ}

lemma mem_of_pow_smul_mem (S : Submodule O (Fin r → O)) (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S)
    (n : ℕ) (v : Fin r → O) (h : ϖ ^ n • v ∈ S) : v ∈ S := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply hS
    rw [smul_smul, ← pow_succ']
    exact h

lemma quotient_isTorsionFree (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : IsTorsionFree O ((Fin r → O) ⧸ S) := by
  have hnz : ∀ (c : O) (v : Fin r → O), c ≠ 0 → c • v ∈ S → v ∈ S := by
    intro c v hc hcv
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
    obtain ⟨u, hu⟩ := hn
    apply mem_of_pow_smul_mem S hS n v
    rw [← hu, mul_comm, mul_smul]
    exact S.smul_mem _ hcv
  constructor
  intro c hc x y hxy
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [← Submodule.Quotient.mk_smul] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  rw [← smul_sub] at hxy
  exact hnz c _ hc.ne_zero hxy

lemma exists_isCompl_of_saturated (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : ∃ Q : Submodule O (Fin r → O), IsCompl S Q := by
  have := quotient_isTorsionFree hϖ S hS
  have : Module.Free O ((Fin r → O) ⧸ S) := Module.free_of_finite_type_torsion_free'
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ (LinearMap.id) S.mkQ_surjective
  refine ⟨LinearMap.range h, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxS ⟨q, rfl⟩
    have hq : q = 0 := by
      have := LinearMap.congr_fun hh q
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [← this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxS
    simp [hq]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - h (S.mkQ x) ∈ S := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply]
      have := LinearMap.congr_fun hh (S.mkQ x)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [this, sub_self]
    have : x = (x - h (S.mkQ x)) + h (S.mkQ x) := by abel
    rw [this]
    exact Submodule.add_mem_sup hx (LinearMap.mem_range_self h _)

end Lattice

end Formalism.ExponentWindows
