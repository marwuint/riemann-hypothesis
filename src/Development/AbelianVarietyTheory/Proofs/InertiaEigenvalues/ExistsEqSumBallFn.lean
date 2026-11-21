import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open ValuativeRel OnePoint

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

open Classical in

def ballFn (a r : k) : OnePoint k → ℂ := fun x =>
  x.elim 0 fun y => if valuation k (y - a) ≤ valuation k r then 1 else 0

@[simp] theorem ballFn_infty (a r : k) : ballFn a r ∞ = 0 := rfl

open Classical in

theorem ballFn_coe (a r x : k) :
    ballFn a r x = if valuation k (x - a) ≤ valuation k r then 1 else 0 := rfl

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocGL.ProjLine
