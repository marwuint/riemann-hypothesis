import Formalism.SharpRestriction.GrowthBounds.RootWeights.PropertySubmoduleWeightEntryComponent

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (weightComponent LL S nu F) = if wtS LL S m = nu then coeff m F else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : coeff m F = 0 <;> simp [h1, h2]

section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W

theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (MvPolynomial.coeff m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
