import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk

noncomputable section

open ValuativeRel
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
open MeasureTheory GlobalTheory.SplitFlip

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k}

end

end GlobalTheory.FullRankCoinv.UnitMinor
