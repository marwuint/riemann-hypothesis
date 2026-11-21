import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def ExtRho : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ ρ : M →ₐ[ℚ] ℂ, ∃ ρ₁ : M₁ →ₐ[ℚ] ℂ, ∀ x : M, ρ₁ (IntermediateField.inclusion h x) = ρ x

def veluF (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)

def veluD (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.derivWeierstrassP z + ∑ P ∈ S, L.derivWeierstrassP (z + P)

def veluU (L : PeriodPair) (S : Finset ℂ) : Set ℂ :=
  {z | z ∉ L.lattice ∧ ∀ P ∈ S, z + P ∉ L.lattice}

def IsogD : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → MulStable L c → IsKerReps L c S →
    ∀ z, c * z ∉ L.lattice → c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z

def TorsDense : Prop :=
  ∀ L : PeriodPair, Dense {t : ℂ | ∃ n : ℕ, 0 < n ∧ (n : ℂ) * t ∈ L.lattice}

def IsogODE : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → (∀ P ∈ S, P ∉ L.lattice) →
    (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) →
    (∀ z ∈ veluU L S, veluD L S z ^ 2 =
      4 * veluF L S z ^ 3 - c ^ 4 * L.g₂ * veluF L S z - c ^ 6 * L.g₃) →
    MulStable L c ∧ (∀ P ∈ S, c * P ∈ L.lattice) ∧
      ∀ z ∈ veluU L S, c * z ∉ L.lattice ∧ c ^ 2 * L.weierstrassP (c * z) = veluF L S z ∧
        c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z

end PI.GalTorsConj.W

end
