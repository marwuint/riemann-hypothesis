import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFrames
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOneStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding toC relab Unf IsUnf GoodEmb rdU laU perFr
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

section Key

open GlobalTheory.KeyFourth GlobalTheory.ShFam

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {r : ℕ} {M : ModelsOf F r} {k : Fin F.n}

instance isLocalRing_cAt : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)

end Key

end GlobalTheory.KeyHol
