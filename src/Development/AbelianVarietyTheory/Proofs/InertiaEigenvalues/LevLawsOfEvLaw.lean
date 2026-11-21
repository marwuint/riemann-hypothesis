import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial

noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

end Concrete

end GlobalTheory.NL
