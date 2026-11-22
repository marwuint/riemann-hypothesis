import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LubinTateSeriesEqOfCoeffOneEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateLogNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open GlobalTheory.MemLoc Formalism.BasicNotions.Examples₂.LB GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjDegree

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

variable (T : LocTied l P AI) (K : FinExt l)

def jB : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))

end GlobalTheory.ConjDegree

end
