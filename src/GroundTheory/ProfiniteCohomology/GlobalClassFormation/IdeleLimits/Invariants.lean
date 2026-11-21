import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SmulOfEqOfMemFixingSubgroup
import GroundTheory.GlobalFields.IdeleClassGroup.Invariants
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleLimit

open FiniteSubfield

theorem smul_of_eq_of_ideleEquiv {M : FiniteSubfield} (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : M.1 ≃+* M.1)
    (h : ∀ x : M.1, σ x = τ x) (x : IdeleGroup M.1) :
    σ • of M x = of M (ideleEquiv τ x) :=
  (smul_of σ M x).trans (of_ideleEquiv_congr _ _ h x)

end IdeleLimit

end

end GroundTheory.ProfCoh
