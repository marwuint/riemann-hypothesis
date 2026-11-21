import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk

noncomputable section

open ValuativeRel
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lastCols (n d : ℕ) (h : n ≤ d) : Fin n ↪ Fin d :=
  ⟨fun i => ⟨d - n + i, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩

theorem lastCols_val (n d : ℕ) (h : n ≤ d) (i : Fin n) : (lastCols n d h i : ℕ) = d - n + i := rfl

section
open MeasureTheory GlobalTheory.SplitFlip

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k}

end

end GlobalTheory.FullRankCoinv.UnitMinor
