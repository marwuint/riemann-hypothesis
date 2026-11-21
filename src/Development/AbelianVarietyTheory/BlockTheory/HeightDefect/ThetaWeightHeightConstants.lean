import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParamsT

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

open Formalism.BasicNotions NumberField

def Lift (R : Ranks) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

def pSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).1

def qSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).2

def rho {R : Ranks} (j : Lift R) : ℕ := R.m - j.1

theorem rho_eq_qSig {R : Ranks} (j : Lift R) : rho j = qSig j := rfl

@[ext] structure ThetaWeight (D : D7) (j : Lift D.R) where
  plus : D.what₂.Tau → Fin (pSig j) → ℤ
  minus : D.what₂.Tau → Fin (qSig j) → ℤ
  plus_anti : ∀ τ, Antitone (plus τ)
  minus_anti : ∀ τ, Antitone (minus τ)
  n : ℕ

namespace ThetaWeight

variable {D : D7} {j : Lift D.R}

def add (G G' : ThetaWeight D j) : ThetaWeight D j where
  plus := G.plus + G'.plus
  minus := G.minus + G'.minus
  plus_anti τ := (G.plus_anti τ).add (G'.plus_anti τ)
  minus_anti τ := (G.minus_anti τ).add (G'.minus_anti τ)
  n := G.n + G'.n

end ThetaWeight

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

end
