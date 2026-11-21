import Formalism.PieriBlockIdeals.StatementTop
import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.QuotientMetricDivisors.ClassSumDualLe
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.CohomologicalDescent.E

open Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

def ExIntervalLt : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w ∧
      (w < l → LA.exZ N N le_rfl (res N lam) l = 0)

def ExCut : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ l : ℕ, l.Prime → ∀ (lo : ℤ) (w : ℕ),
    (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
    ∀ a : ℕ, a ≤ N →
      LA.exZ N N le_rfl (res N lam) l ≤
        LA.exZ a a le_rfl (res a lam) l +
          LA.exZ (N - a) (N - a) le_rfl (res (N - a) (fun i => lam (a + i))) l +
          a * (N - a) * Nat.log l w

end Formalism.CohomologicalDescent.E
