import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem lowestKTypes_jointShape : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ IsParam (lamM' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) := by
  intro t al be ga de h
  obtain ⟨hA, hpA, hpA', -, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de h
  obtain ⟨hM, hpM', -, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de h
  exact ⟨⟨hpA, hpA', hpM'⟩, hA, hM⟩

end GlobalTheory
