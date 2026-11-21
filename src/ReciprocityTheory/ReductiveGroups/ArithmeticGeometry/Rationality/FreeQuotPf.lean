import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
import Lemmata.MiscLemmasJ.Imports

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Module

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem freeQuot_exists_smul_mem (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx

theorem freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by
  set T := Submodule.span F (S : Set X)
  have hST : S ≤ T.restrictScalars R := fun x hx => Submodule.subset_span hx
  let S' : Submodule R (T.restrictScalars R) := S.comap (T.restrictScalars R).subtype
  have h0 : Module.rank R ((T.restrictScalars R) ⧸ S') = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem S (y.2 : (y : X) ∈ T)
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd'
  have h1 := rank_quotient_add_rank_of_isDomain S'
  rw [h0, zero_add, (Submodule.comapSubtypeEquivOfLe hST).rank_eq] at h1
  rw [h1, IsLocalization.rank_eq (N := T) F (nonZeroDivisors R) le_rfl]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
