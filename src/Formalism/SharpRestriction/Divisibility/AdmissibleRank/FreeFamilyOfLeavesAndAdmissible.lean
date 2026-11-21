import Mathlib
import Formalism.PeriodIntegrals.ParahoricIdxZ
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.CardRangeRedJ
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitarySecondCountable.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralSpanAlgebra.Burnside
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.GoodPartEigenspaceKernelSplitting
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

set_option linter.unusedVariables false

namespace Formalism.MainNotions.DIV

end Formalism.MainNotions.DIV

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem archimedean_statement_iff_local (D : D7) (X : Formalism.MainNotions.SchurIrreducible.Prov D) :
    Formalism.MainNotions.SchurIrreducible.Stmt D X ↔ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisLocal D X := Iff.rfl

def Qof (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Submodule ℂ (D.what₂.Amb μ) :=
  D.what₂.V0 μ ⊓ (D.what₂.V0 μ ⊓ LinearMap.ker ι)ᗮ

def BijOn (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Prop :=
  Function.Bijective (ι.domRestrict (Qof D μ ι))

end Formalism.MainNotions.DIV

end

namespace Formalism.MainNotions.DIV

end Formalism.MainNotions.DIV

