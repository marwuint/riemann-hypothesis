import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj

set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair
namespace UpperTheory.GalS
theorem cusp_of_pair_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (hP : _root_.UpperTheory.GalS.PairUAlt) : _root_.UpperTheory.GalS.CuspUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
  exact hP E Ω l ι a ha π χ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩
theorem carU_of_finite_gl_recT : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.UpperTheory.GalS.CarUAlt → _root_.UpperTheory.GalS.CarUAlt := fun _ _ h => h
theorem carU_of_regular_algebraic_purity (H : _root_.UpperTheory.GalS.CarUAlt) (_ : GlobalTheory.Published.RegularAlgebraicPurity) : _root_.UpperTheory.GalS.CarUAlt := H
end UpperTheory.GalS
end
