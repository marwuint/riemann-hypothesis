import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.PairingProductCorollary

open Finset
open scoped ComplexOrder

noncomputable section

def cg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (a : Fin K) : ℝ :=
  ∑ i, |F7.lagCo (grid a) i|

def coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.lagCo (grid a) (j a)

def qProd {K d : ℕ} (q : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.qW q w (grid a (j a))

def nnProd {K d : ℕ} (nn : ℝ → ℝ) (h : ℝ) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, nn (grid a (j a) + h)

def LowerBlockNormalisedBoundFromComponents : Prop :=
  ∀ (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (q nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (o W0 : ℂ)
    (RL RV : (Fin K → Fin (d + 1)) → ℝ) (wt wt' bw Qw BB : ℝ),
    (∀ a, Function.Injective (grid a)) →
    (∀ a i, 0 < q (grid a i) ∧ 0 < F7.qW q w (grid a i) ∧ 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1)) →
    (∀ a i, q (grid a i) ≤ Qw * F7.qW q w (grid a i)) →
    (∀ a i, nn (grid a i) * nn (grid a i + 1) / q (grid a i) ≤ BB ^ 2) →
    0 ≤ BB → 0 ≤ wt → 0 ≤ wt' → 0 < bw → (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    ‖o‖ ^ K * ‖W0‖ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) →
    ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) ≤
      (∏ a, cg grid a) * (Real.sqrt Qw * BB) ^ K *
        ∑ j, F7.thGrid grid j *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)

def PairingGramInequality (Ntt : ℂ) (Nt Nt' : ℝ) : Prop := ‖Ntt‖ ^ 2 ≤ Nt * Nt'

def minFac (L o : ℝ) (K : ℕ) : ℝ := if L < o then (L / o) ^ K else 1

def oAbs {ι : Type} (t t' : ι → ℂ) (v : ι) : ℝ := ‖1 / t v - 1 / t' v‖

def LeadingBlockSeveralPlacesBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ : ι → ℝ) (t t' : ι → ℂ) (Ntt : ℂ)
    (Nt Nt' S1 S2 : ℝ),
    (∀ v, t v ≠ 0 ∧ t' v ≠ 0) → (∀ v, 0 ≤ abelian₂ v) → 0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S1 → 0 ≤ S2 →
    PairingGramInequality Ntt Nt Nt' →
    Nt ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1 →
    Nt' ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2 →
    ‖Ntt‖ ≤ (∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K) * ((S1 + S2) / 2)

end

end Formalism.FourierDecayAlt.PairingProductCorollary
