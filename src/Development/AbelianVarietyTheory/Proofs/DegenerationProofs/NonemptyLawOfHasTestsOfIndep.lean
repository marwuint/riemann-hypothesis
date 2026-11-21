import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestCartOfSpecialFibreSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := _root_.GlobalTheory.ZJ.Core.fib_of_indep C hI
  have hS := _root_.GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests C hT hF
  have hC : C.TestCart := _root_.GlobalTheory.ZJ.Core.testCart_of_fib C hF hS
  have hL : C.FibLaw := _root_.GlobalTheory.ZJ.Core.fibLaw_of_testCart C hC
  exact _root_.GlobalTheory.ZJ.Core.nonempty_law C hS hC (_root_.GlobalTheory.ZJ.Core.exists_add_extension C hT hS hC hL) (_root_.GlobalTheory.exists_inv_extension C hT hS hC hL)

end GlobalTheory.ZJ
