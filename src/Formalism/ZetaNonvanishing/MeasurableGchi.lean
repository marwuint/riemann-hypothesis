import Formalism.DefsOC
import Formalism.ZetaNonvanishing.Assembly

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

lemma Sz_eq_Sa : Sz = Sa (fun n => Λ n) := rfl

lemma Schi_eq_Sa {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Schi χ = Sa (fun n => Λ n * (χ n).re) := rfl

end Formalism
