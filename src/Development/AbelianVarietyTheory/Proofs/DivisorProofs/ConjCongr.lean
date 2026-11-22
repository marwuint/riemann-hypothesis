import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal
open scoped Formalism.Per

namespace GlobalTheory.ConjPeriod

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def uj (T : LocTied l P AI) (j : ℕ) : Per.Acris l →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp
    (T.eB.symm.toRingHom.comp ((algebraMap (Per.Acris l) (Per.Bcris l)).comp (GlobalTheory.MemLoc.phiA l ^ j)))

end GlobalTheory.ConjPeriod

end
