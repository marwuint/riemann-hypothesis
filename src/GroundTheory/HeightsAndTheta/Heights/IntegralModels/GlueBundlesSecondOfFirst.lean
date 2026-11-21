import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Concrete

variable (X : Scheme.{0}) (S : Finset Nat.Primes)

theorem GlueBundles.primeProd_cast : GroundTheory.Heights₂.Heights.Model.primeProd S = ((primeProd S : ℕ) : ℤ) := by
  simp [GroundTheory.Heights₂.Heights.Model.primeProd, primeProd]

theorem GlueBundles.invOpen_eq :
    GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X) (GroundTheory.Heights₂.Heights.Model.primeProd S) =
      invOpen X (primeProd S) := by
  rw [GroundTheory.Heights₂.Heights.Model.invOpen, invOpen, GlueBundles.primeProd_cast]

theorem GlueBundles.genOpen_eq_top : genOpen X (primeProd S) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hsub := GroundTheory.Heights₂.Heights.Model.range_baseChangeMap_subset (toSpecZ X) ℚ
    (GroundTheory.Heights₂.Heights.Model.primeProd S)
    (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
      (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)) ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, GlueBundles.invOpen_eq] at hsub
  exact hsub

instance GlueBundles.isIso_genOpen_ι : IsIso (genOpen X (primeProd S)).ι := by
  rw [GlueBundles.genOpen_eq_top, ← Scheme.topIso_hom]
  infer_instance

end Concrete

end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
