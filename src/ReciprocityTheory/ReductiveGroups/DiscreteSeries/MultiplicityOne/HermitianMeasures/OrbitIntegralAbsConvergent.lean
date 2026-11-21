import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

def dimN (k r : ℕ) : ℕ := r * (2 * r + 2 * k + 1)

def bS (k r : ℕ) : ℝ := ((2 * r + k : ℕ) : ℝ) * (dimN k r : ℝ)

def q0 (k r : ℕ) : ℕ := min (k + r) (r + 1)

def SIntFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ b : ℝ, bS k r < b →
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN)) < ∞ ∧
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ∂(μW.prod μN)) < ∞

variable {k r : ℕ}

theorem bS_le (k r : ℕ) : bS k r ≤ 2 * (r : ℝ) * ReciprocityTheory.ChartRestriction.DS.Mult1.nR k r ^ 2 := by
  have h : (2 * r + k) * (r * (2 * r + 2 * k + 1)) ≤ 2 * r * (2 * r + k + 1) ^ 2 := by
    nlinarith [Nat.zero_le (r * r * r), Nat.zero_le (r * r * k), Nat.zero_le (r * k * k), Nat.zero_le (k * k * k),
      Nat.zero_le (r * r), Nat.zero_le (r * k), Nat.zero_le (k * k), Nat.zero_le r, Nat.zero_le k]
  unfold bS dimN ReciprocityTheory.ChartRestriction.DS.Mult1.nR
  exact_mod_cast h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0
