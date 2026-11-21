import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def domC (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort (fun a => -x a)

def spinSq (ν : Fin n → ℝ) : ℝ := nsq (domC (ν - rhoV n) + rhoV n)

def LSq (lam : Fin n → ℤ) : ℝ := nsq fun a => 2 * ((lam a : ℝ) + rhoV n a)

open Classical in

def topTypes (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  (((univ : Finset (Finset (Fin n × Fin n))).filter fun B => ∀ p ∈ B, p.1 < p.2).image fun B =>
    domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB B) - rhoV n).filter fun ν => StrictAnti (ν + rhoV n)

def LemmaHT : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam ∧
    ∀ ν ∈ topTypes lam, spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam)

def SecondTypeWeightsShorter : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν, IsSecondTypeWeight lam lev ν →
    ν ∈ topTypes lam ∧ nsq (ν + rhoV n) < nsq (muQ lam lev + rhoV n)

end PositivityTheory.RgBcC.RealD
