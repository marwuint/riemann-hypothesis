import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.FormInner

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_reps (J : Subgroup (GAf L n)) (S : Finset (GAf L n))
    (hS : ∀ g : GAf L n, ∃ s ∈ S, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * s * κ) :
    ∃ T, IsClassReps J T := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)) := DoubleCoset.mk (GQ L n) J
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ b = (γ : GAf L n) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem relIndex_ne_zero_of_reps {J K : Subgroup (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) {T : Finset (GAf L n)}
    (hT : IsClassReps K T) : K.relIndex J ≠ 0 := by
  classical
  have hfin : ∀ t : GAf L n, {γ : GQ L n | (γ : GAf L n) * t ∈ J}.Finite := by
    intro t
    rcases Set.eq_empty_or_nonempty {γ : GQ L n | (γ : GAf L n) * t ∈ J} with h | ⟨γ₀, h₀⟩
    · rw [h]; exact Set.finite_empty
    · haveI := GlobalTheory.StabFin.finite_conj_mem L n J hJ 1
      refine Set.Finite.subset (Set.finite_range fun δ : {γ : GQ L n // (1 : GAf L n)⁻¹ * (γ : GAf L n) * 1 ∈ J} => δ.1 * γ₀) ?_
      intro γ hγ
      refine ⟨⟨γ * γ₀⁻¹, ?_⟩, by simp⟩
      have := J.mul_mem hγ (J.inv_mem h₀)
      simpa [mul_assoc] using this
  refine relIndex_ne_zero_of_cover (T.biUnion fun t => (hfin t).toFinset.image fun γ : GQ L n => (γ : GAf L n) * t) (fun κ hκ => ?_) hle
  obtain ⟨t, ⟨ht, γ, k, hk, e⟩, -⟩ := hT κ
  refine ⟨γ * t, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).2 ?_)⟩, by rw [e, inv_mul_cancel_left]; exact hk⟩
  have := J.mul_mem hκ (J.inv_mem (hle hk))
  rw [e] at this
  simpa using this

theorem form_inv {a : NG.AlgWt L n} (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) {J : Subgroup (GAf L n)} (hJ : IsBounded J) {χ : J →* ℂˣ}
    {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    ∀ κ ∈ J, ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g) := by
  intro κ hκ g
  have e : ∀ k : J, f (g * k) = ((χ k : ℂˣ) : ℂ) • f g := fun k => congrFun (hf.2 k) g
  have e' : f' (g * κ) = ((χ ⟨κ, hκ⟩ : ℂˣ) : ℂ) • f' g := congrFun (hf'.2 ⟨κ, hκ⟩) g
  rw [e ⟨κ, hκ⟩, e']
  by_cases h0 : f g = 0
  · simp [h0]
  obtain ⟨N, hN, hinv⟩ := hf.1.2
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  have hle : J ⊓ congSub L n N ≤ J := inf_le_left
  have hne : (J ⊓ congSub L n N).relIndex J ≠ 0 := by
    classical
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N) → u ∈ J ∧ f₀⁻¹ * u ∈ congSub L n N := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) hle
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, J.mul_mem (J.inv_mem h2) hκ, ?_⟩
    have := (congSub L n N).mul_mem ((congSub L n N).inv_mem h3) h₁
    simpa [mul_assoc] using this
  have hn := norm_eq_one_of_relIndex hle hne χ (fun k hk => by
    have h1 := e ⟨k, hle hk⟩
    rw [hinv k hk.2 g] at h1
    have h2 : (((χ ⟨k, hle hk⟩ : ℂˣ) : ℂ) - 1) • f g = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact Units.ext (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0))) ⟨κ, hκ⟩
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.conj_mul', hn]
  simp

end GlobalTheory.FormInner

end
