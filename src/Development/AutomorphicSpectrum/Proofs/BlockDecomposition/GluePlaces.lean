import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.DualWhittakerAdelicGL3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.GlueSign

section Sym

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

instance isAbelianGalois_quadratic : IsAbelianGalois ℚ K := {}

end Sym

end GlobalTheory.CompanionTheory.GlueSign
