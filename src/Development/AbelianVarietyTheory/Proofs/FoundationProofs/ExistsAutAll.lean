import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation

noncomputable section

namespace GlobalTheory.K5.Rel

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def IsGen (T : Tower p Ω) (m s : ℕ) (τ γ : Gal p Ω) : Prop :=
  (∀ n, τ (T.ζ n) = T.ζ n) ∧ (∀ n, τ (T.qq n) = T.ζ n ^ (p ^ s) * T.qq n) ∧
  (∀ n, γ (T.ζ n) = T.ζ n ^ (1 + p ^ m)) ∧ ∀ n, γ (T.qq n) = T.qq n

variable {T : Tower p Ω} {m s : ℕ} {τ γ : Gal p Ω}

end GlobalTheory.K5.Rel
