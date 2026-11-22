import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LiftingTheory

section PhiBC

theorem phib_smodeq {M : Type} [CommRing M] (c x y : M) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {c}) ^ k • ⊤ : Submodule M M)] ↔ c ^ k ∣ x - y := Formalism.MainNotions.LiftingTheory.phib_smodeq c x y k

theorem phib_complete {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) :
    IsAdicComplete (Ideal.span {algebraMap R M ϖ}) M := by
  have key : ∀ (x : M) (k : ℕ), (algebraMap R M ϖ) ^ k ∣ x ↔ ∀ j, ϖ ^ k ∣ b.equivFun x j := by
    intro x k
    constructor
    · rintro ⟨z, rfl⟩ j
      refine ⟨b.equivFun z j, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, map_smul]
      rfl
    · intro h
      choose d hd using h
      refine ⟨b.equivFun.symm d, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      rw [hd j]
      rfl
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.equivFun.injective
    rw [map_zero]
    funext j
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) R)
    intro k
    rw [phib_smodeq, sub_zero]
    have h := hx k
    rw [phib_smodeq, sub_zero] at h
    exact (key x k).1 h j
  · intro f hf
    have hc : ∀ j, ∃ L : R, ∀ k,
        b.equivFun (f k) j ≡ L [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule R R)] := by
      intro j
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) R)
      intro m k hmk
      rw [phib_smodeq]
      have h := hf hmk
      rw [phib_smodeq] at h
      have h' := (key _ m).1 h j
      rwa [map_sub] at h'
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun k => ?_⟩
    rw [phib_smodeq, key]
    intro j
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply]
    exact (phib_smodeq _ _ _ _).1 (hL j k)

theorem phib_OL_complete {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := Formalism.MainNotions.LiftingTheory.phib_OL_complete LL

end PhiBC

end Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

end
