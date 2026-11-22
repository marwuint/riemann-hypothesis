import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LubinTateSeriesEqOfCoeffOneEq

noncomputable section

namespace GlobalTheory.LTOmega

section Core

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Prism GlobalTheory.AinfK GlobalTheory.LTTilt GlobalTheory.PZ GlobalTheory.Per.AinfComplete
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {π : ↥(OL K)}

end Core

end GlobalTheory.LTOmega
