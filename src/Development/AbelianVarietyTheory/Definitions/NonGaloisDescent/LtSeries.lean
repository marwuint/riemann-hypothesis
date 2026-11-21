import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PZ

variable {l : ℕ} [Fact l.Prime]

def lineRep {K : FinExt l} {LL : FinExt l} (χ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) where
  toFun g := ((χ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp; ring

end GlobalTheory.PZ

end
