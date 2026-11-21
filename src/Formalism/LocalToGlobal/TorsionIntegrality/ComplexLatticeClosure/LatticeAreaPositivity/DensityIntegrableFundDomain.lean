import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice

noncomputable section
open scoped ComplexConjugate Pointwise
open MeasureTheory

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

instance (L : PeriodPair) : Countable L.lattice.toAddSubgroup := (inferInstance : Countable L.lattice)

end Formalism.L2.Th1.F2
