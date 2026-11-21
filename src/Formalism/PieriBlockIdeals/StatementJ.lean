import Formalism.RankGapBounds.LargePrimeFactor
import Formalism.PieriBlockIdeals.Statement
import Formalism.RankGapBounds.CloudMinFalse

open Finset

namespace Formalism.CohomologicalDescent.Joint

open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt

noncomputable section

structure Weights {ι : Type} (D : Data ι) where

  U : ι → Fin D.Nr → ℤ

  anti : ∀ τ, StrictAnti (U τ)

  inRange : ∀ τ a, 0 ≤ U τ a ∧ U τ a ≤ (D.h : ℤ)

  k_le : D.k ≤ D.Nr

  cloudIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, (a : ℕ) < D.k → D.xlo τ ≤ U τ a ∧ U τ a ≤ D.xhi τ

  cloudWidth : ∀ τ ∈ D.T2, D.xhi τ - D.xlo τ ≤ (D.S : ℤ)

  restLo : ι → ℤ

  restIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, D.k ≤ (a : ℕ) →
    restLo τ ≤ U τ a ∧ U τ a ≤ restLo τ + (D.eta' : ℤ)

  Wd : ℕ

  thinLo : ι → ℤ

  thinIn : ∀ τ, τ ∉ D.T2 → ∀ a : Fin D.Nr, thinLo τ ≤ U τ a ∧ U τ a ≤ thinLo τ + (Wd : ℤ)

  thinWidth : Wd + D.Nr ≤ D.Wthin

def Weights.set {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Finset ℤ :=
  Finset.univ.image (W.U τ)

structure Windows {ι : Type} (D : Data ι) (W : Weights D) where
  minB : ι → ℤ

  maxB_eq : ∀ τ, D.maxB τ = minB τ + (D.t : ℤ) - 1
  UF : ι → ℕ → Fin D.Nr → ℤ
  minBF : ι → ℕ → ℤ
  mw_eq : ∀ τ l, D.mw τ l = Formalism.CohomologicalDescent.mwCount l (minB τ) D.t (D.kap l) (W.set τ)
  mwF_eq : ∀ τ l, D.mwF τ l =
    Formalism.CohomologicalDescent.mwCount l (minBF τ l) D.t (D.kap l) (Finset.univ.image (UF τ l))

end

end Formalism.CohomologicalDescent.Joint
