import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes NumberField

def CycSplit : Prop :=
  ∀ (N p : ℕ) (K : Type) [Field K] [NumberField K] [Algebra K (CyclotomicField N ℚ)], 0 < N → p.Prime →
    p % N = 1 % N →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
