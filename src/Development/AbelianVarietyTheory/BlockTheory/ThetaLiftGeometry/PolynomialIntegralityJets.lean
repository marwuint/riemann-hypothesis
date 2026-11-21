import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
