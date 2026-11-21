import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLx
import Mathlib
import Formalism.FormalDegreeBessel.FinalDS

open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HasTypeU (k : ℕ) (u : Fin k → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π

def HighestWeightExists : Prop := ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u → HasTypeU k u

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + Formalism.REAL.rhoC ε) a - (Λ + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ))

def LowKMultOne : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'

section FiniteOrderMat

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {N : Type*} [Fintype N] [DecidableEq N]

structure UnramAt (ϖ : R) (p : ℕ) : Prop where
  prime : Prime ϖ
  sep : ∀ x : R, (∀ n : ℕ, ϖ ^ n ∣ x) → x = 0
  pPrime : p.Prime
  three_le : 3 ≤ p
  unram : ∃ u : R, ¬ ϖ ∣ u ∧ (p : R) = u * ϖ
  other : ∀ l : ℕ, l.Prime → l ≠ p → ¬ ϖ ∣ (l : R)

end FiniteOrderMat

end Formalism.MainNotions.DiscreteSeriesWeylDimension

end
