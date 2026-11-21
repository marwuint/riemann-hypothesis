import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}

def LocalValuationBoundAt (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt t, Dc.Pt u t φ F = 0 ∨ sgw ≤ (vw w (Dc.Pt u t φ F) : ℝ)

end Final

end Formalism.L2.DIV
