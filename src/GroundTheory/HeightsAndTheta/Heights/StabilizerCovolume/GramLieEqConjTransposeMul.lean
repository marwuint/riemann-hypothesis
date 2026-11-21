import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexConjugate ComplexOrder

namespace HermDatum

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
  (A : HermDatum Em Ψ N j)

omit [NumberField Em] [IsCMField Em] in
theorem conj_comp_conj_comp (σ : Em →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
  ext x
  simp

def embEquiv : Ψ ⊕ Ψ ≃ (Em →+* ℂ) :=
  Equiv.ofBijective (Sum.elim A.emb fun τ => (starRingEnd ℂ).comp (A.emb τ)) (by
    constructor
    · rintro (τ | τ) (τ' | τ') h
      · simp only [Sum.elim_inl] at h
        exact congrArg Sum.inl (A.emb_inj h)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        exact absurd ⟨τ, h⟩ ((A.cmType (A.emb τ')).1 ⟨τ', rfl⟩)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        exact absurd ⟨τ', h.symm⟩ ((A.cmType (A.emb τ)).1 ⟨τ, rfl⟩)
      · simp only [Sum.elim_inr] at h
        have h' : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (A.emb τ)) =
            (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (A.emb τ')) := by rw [h]
        rw [conj_comp_conj_comp, conj_comp_conj_comp] at h'
        exact congrArg Sum.inr (A.emb_inj h')
    · intro σ
      by_cases h : ∃ τ, A.emb τ = σ
      · obtain ⟨τ, rfl⟩ := h
        exact ⟨Sum.inl τ, rfl⟩
      · have h2 : ∃ τ, A.emb τ = (starRingEnd ℂ).comp σ := by
          by_contra h'
          exact h ((A.cmType σ).2 h')
        obtain ⟨τ, hτ⟩ := h2
        refine ⟨Sum.inr τ, ?_⟩
        show (starRingEnd ℂ).comp (A.emb τ) = σ
        rw [hτ, conj_comp_conj_comp])

@[simp] theorem embEquiv_inl (τ : Ψ) : A.embEquiv (Sum.inl τ) = A.emb τ := rfl

@[simp] theorem embEquiv_inr (τ : Ψ) : A.embEquiv (Sum.inr τ) = (starRingEnd ℂ).comp (A.emb τ) := rfl

end HermDatum

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

theorem hodgeInner_add_left (z : (Σ k, ι k) → ℂ) (v v' w : Fin D.N → Em) :
    D.hodgeInner z (v + v') w = D.hodgeInner z v w + D.hodgeInner z v' w := by
  have h : ∀ τ, (fun b => D.herm.emb τ (v b) + D.herm.emb τ (v' b)) =
      (fun b => D.herm.emb τ (v b)) + fun b => D.herm.emb τ (v' b) := by
    intro τ; rfl
  simp only [hodgeInner, Pi.add_apply, map_add, h, Matrix.mulVec_add, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib, Complex.add_re, mul_add]

theorem hodgeInner_add_right (z : (Σ k, ι k) → ℂ) (v w w' : Fin D.N → Em) :
    D.hodgeInner z v (w + w') = D.hodgeInner z v w + D.hodgeInner z v w' := by
  have h : ∀ τ, (fun b => D.herm.emb τ (w b) + D.herm.emb τ (w' b)) =
      (fun b => D.herm.emb τ (w b)) + fun b => D.herm.emb τ (w' b) := by
    intro τ; rfl
  simp only [hodgeInner, Pi.add_apply, map_add, h, Matrix.mulVec_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Complex.add_re]

def hodgeAdd (z : (Σ k, ι k) → ℂ) : (Fin D.N → Em) →+ (Fin D.N → Em) →+ ℝ :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (D.hodgeInner z v) (D.hodgeInner_add_right z v))
    (fun v v' => AddMonoidHom.ext fun w => D.hodgeInner_add_left z v v' w)

@[simp] theorem hodgeAdd_apply (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) :
    D.hodgeAdd z v w = D.hodgeInner z v w := rfl

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
