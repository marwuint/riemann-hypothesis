import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Filter Topology

namespace GlobalTheory.PZ.LTModel

theorem lineRep_apply {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (χ : ↥(GK K) →* (↥LL.1)ˣ) (g : ↥(GK K))
    (v : Fin 1 → ↥LL.1) : lineRep χ g v = (χ g : ↥LL.1) • v := rfl

end GlobalTheory.PZ.LTModel

end
