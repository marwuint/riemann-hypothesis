import Mathlib
import Formalism.HarderNarasimhan.StatementPl
import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.slopeLatticeData

open Formalism.HN

abbrev FinPl (K : Type) [Field K] [NumberField K] := {p : Ideal (𝓞 K) // p.IsMaximal}

def idealPow {K : Type} [Field K] [NumberField K] (n : FinPl K →₀ ℤ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  n.prod fun w k => ((w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ^ k

def ell {K : Type} [Field K] [NumberField K] (w : FinPl K) : ℝ :=
  Real.log (Ideal.absNorm w.1 : ℝ) / (Module.finrank ℚ K : ℝ)

def modLat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (σ : FinPl K →₀ ℤ) (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Formalism.HermitianLatticesTheory.idealSmul ((idealPow (-σ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) N

def lenAt {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : FinPl K) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  haveI := w.2.isPrime
  Module.length (Localization.AtPrime w.1)
    (LocalizedModule w.1.primeCompl (A ⧸ B.comap A.subtype))

abbrev Rloc {K : Type} [Field K] [NumberField K] (w : FinPl K) : Type :=
  @Localization.AtPrime (𝓞 K) _ w.1 w.2.isPrime

end Formalism.LFunctionChainParameters.slopeLatticeData
