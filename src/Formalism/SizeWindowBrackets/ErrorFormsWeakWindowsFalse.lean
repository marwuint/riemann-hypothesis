import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis

open Real

namespace Formalism.LFunctionChainParameters.LErr

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

noncomputable section

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}

def ErrText (D : Data U0 W Top m f) : ℝ :=
  D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) + (m : ℝ) * (D.B0 + D.Nc)

def CErr (C : Consts) : ℝ := C.eDiv + C.eLoss + 3

def KBig (K cHH eK : ℝ) : ℝ := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK)

def ConstsBound (C : Consts) (K : ℝ) : Prop :=
  0 ≤ C.cDiv ∧ C.cDiv ≤ K ∧ 0 ≤ C.cE ∧ C.cE ≤ K ∧ 0 ≤ C.cH ∧ C.cH ≤ K ∧
  0 ≤ C.cCount ∧ C.cCount ≤ K ∧ 0 ≤ C.cSlope ∧ C.cSlope ≤ K ∧ 0 ≤ C.cSl1 ∧ C.cSl1 ≤ K ∧
  0 ≤ C.cLoss ∧ C.cLoss ≤ K ∧ 0 ≤ C.eDiv ∧ 0 ≤ C.eLoss ∧ 0 ≤ C.cHH

def ErrWindows0 (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  1 ≤ D.x ∧ 0 < D.ε ∧ D.ε ≤ 1 ∧
  1 ≤ D.b ∧ D.x * D.b ≤ D.a ∧
  1 ≤ D.nT ∧
  (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ∧ D.x * m ≤ D.k ∧
  0 ≤ eK ∧ 1 ≤ D.k ∧ D.k ≤ D.x ^ eK ∧ D.k ≤ D.a ∧
  0 ≤ D.L ∧ D.L ≤ 2 * D.x ^ D.ε ∧ 0 ≤ D.La ∧ D.La ≤ 2 * D.x ^ D.ε ∧
  0 ≤ D.b' ∧ D.k * D.b' ≤ D.a ∧
  0 ≤ Xpp ∧ Xpp ≤ D.a ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.B0 ∧ 0 ≤ D.Nc ∧
  (∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2) ∧
  D.delBar ≤ 1 / 2 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧
  ConstsBound C K

def ErrWindows (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧
  (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * D.x ^ D.ε * (D.nT * D.a)

end

def LargeX (x ε K cHH eK : ℝ) : Prop := Real.log x ≤ x ^ ε ∧ KBig K cHH eK ≤ x ^ ε

def LargeXEv : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → LargeX x ε K cHH eK

def bTx (x ε : ℝ) : ℝ := Real.exp (x ^ ε)

def aTx (x ε : ℝ) : ℝ := x * bTx x ε

def XpTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 3))

def bpTx (x ε : ℝ) : ℝ := aTx x ε / XpTx x ε

def wppTx (x ε n : ℝ) : ℝ := bpTx x ε / (x * n)

def XppTx (x ε n : ℝ) : ℝ := aTx x ε / wppTx x ε n

section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def errorBracketSizeWindows (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))

end

end

end Formalism.LFunctionChainParameters.LErr
