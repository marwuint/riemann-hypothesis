import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact _root_.GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc κ hH hF (_root_.GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait κ hU (_root_.GlobalTheory.KeyEven.keyTrait_of_keyTraitU κ (_root_.GlobalTheory.KeyEven.keyTraitU_of_kapF κ (_root_.GlobalTheory.MBLow.KapFPf.kapF_of_rule4 κ h4))))

end GlobalTheory.KeyEvenClosing
