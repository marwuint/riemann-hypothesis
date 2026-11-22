import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCou
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThmUOfAllSet
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem thmU_and_uTors : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := _root_.GlobalTheory.allSixLaws
  refine ⟨GlobalTheory.ZH.thmU_of_allSet L GlobalTheory.homExtension_semiAbelian_dvr ?_, _root_.GlobalTheory.ZH.uTors_of_laws L L2 L3 L4 L5⟩
  have h := _root_.GlobalTheory.UU.exists_degData_unif (_root_.GlobalTheory.UU.TorsionCount.card_torsion_points L.globalFns L.rigidity) L L2
  intro V _ _ _ A G _ _ s
  obtain ⟨D, U, -, hg, -⟩ := h V A G s
  exact ⟨D, U, hg⟩

end GlobalTheory.ZH
