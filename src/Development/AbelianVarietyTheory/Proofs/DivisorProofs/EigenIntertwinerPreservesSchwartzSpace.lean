import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationIntertwines

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTr

theorem extEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (e : V →ₗ[ℂ] V) (h : Set.BijOn e S S) :
    ∃ T : V ≃ₗ[ℂ] V, (∀ x ∈ S, T x = e x) ∧ ∀ x, x ∈ S ↔ T x ∈ S := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  let f : V →ₗ[ℂ] V := LinearMap.ofIsCompl hQ (e ∘ₗ S.subtype) Q.subtype
  have dec : ∀ x : V, ∃ s ∈ S, ∃ q ∈ Q, x = s + q := fun x => by
    have : x ∈ S ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨s, hs, q, hq, rfl⟩
  have hf : ∀ s ∈ S, ∀ q ∈ Q, f (s + q) = e s + q := fun s hs q hq => by
    rw [map_add, LinearMap.ofIsCompl_apply_left hQ (⟨s, hs⟩ : S), LinearMap.ofIsCompl_apply_right hQ (⟨q, hq⟩ : Q)]
    rfl
  have hdisj : ∀ y ∈ S, y ∈ Q → y = 0 := fun y h1 h2 => by
    have := hQ.inf_eq_bot
    exact (Submodule.mem_bot ℂ).1 (this ▸ Submodule.mem_inf.2 ⟨h1, h2⟩)
  have hmem : ∀ x, x ∈ S ↔ f x ∈ S := by
    intro x
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    rw [hf s hs q hq]
    constructor
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx hs) hq
      subst hq0
      simpa using h.mapsTo hs
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx (h.mapsTo hs)) hq
      subst hq0
      simpa using hs
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxS : x ∈ S := (hmem x).2 (hx ▸ S.zero_mem)
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hxS hs) hq
    subst hq0
    rw [add_zero] at hx ⊢
    have h0 := hf s hs 0 Q.zero_mem
    rw [add_zero, add_zero] at h0
    rw [h0] at hx
    exact h.injOn hs S.zero_mem (by rw [hx, map_zero])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨s', hs', q, hq, rfl⟩ := dec y
    obtain ⟨s, hs, rfl⟩ := h.surjOn hs'
    exact ⟨s + q, hf s hs q hq⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x hx => ?_, hmem⟩
  show f x = e x
  have := hf x hx 0 Q.zero_mem
  rwa [add_zero, add_zero] at this

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

end GlobalTheory.ModelTr

end
