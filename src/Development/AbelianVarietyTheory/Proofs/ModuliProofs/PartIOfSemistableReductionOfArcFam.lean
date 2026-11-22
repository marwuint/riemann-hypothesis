import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelsOfSemistableReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLaws

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem partI_of_semistableReduction_of_arcFam :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ArcFamSt → PartI :=
  fun S A => by
    obtain ⟨L, L2, L3, L4, L5, L6⟩ := _root_.GlobalTheory.allSixLaws
    exact _root_.GlobalTheory.LN.partI_of_inputs _root_.GlobalTheory.twistBaseChange L L2 L3 L4 L5 L6 GlobalTheory.LN.ega_holds
      GlobalTheory.uniformisation_dvr_unconditional _root_.GlobalTheory.LN.pelSt_holds _root_.GlobalTheory.homExtension_semiAbelian_dvr A
      (GlobalTheory.modelsSt_of_semistableReduction S) _root_.GlobalTheory.Moduli.siegelFamilies_closed

end GlobalTheory
