import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
