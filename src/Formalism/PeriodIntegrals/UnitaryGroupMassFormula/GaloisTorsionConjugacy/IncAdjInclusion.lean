import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial

def incAdj (M M₁ : IntermediateField ℚ ℂ) : M₁ →+* IntermediateField.adjoin M (M₁ : Set ℂ) where
  toFun x := ⟨x, IntermediateField.subset_adjoin M _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem extRho : ExtRho := by
  intro M M₁ h halg ρ
  letI iA : Algebra M M₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI hA : Algebra.IsAlgebraic M M₁ := by
    refine ⟨fun x => ?_⟩
    let f : M₁ →ₐ[M] ℂ :=
      { toRingHom := (M₁.val : M₁ →+* ℂ)
        commutes' := fun _ => rfl }
    exact (isAlgebraic_algHom_iff f M₁.val.injective).mp (halg x x.2)
  letI iC : Algebra M ℂ := ρ.toRingHom.toAlgebra
  let φ : M₁ →ₐ[M] ℂ := IsAlgClosed.lift
  refine ⟨{ toRingHom := φ.toRingHom, commutes' := φ.toRingHom.map_rat_algebraMap }, fun x => ?_⟩
  exact φ.commutes x

end PI.GalTorsConj.W

end
