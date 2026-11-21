import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def perp {m : Type} [Fintype m] (ψ : AddChar k Circle) (U₀ : Submodule 𝒪[k] (m → k)) : AddSubgroup (m → k) where
  carrier := {β | ∀ u ∈ U₀, ψ (u ⬝ᵥ β) = 1}
  add_mem' := fun {x y} hx hy u hu => by
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx u hu, hy u hu, one_mul]
  zero_mem' := fun u _ => by simp
  neg_mem' := fun {x} hx u hu => by rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx u hu, inv_one]

def IsReps {V : Type} [AddCommGroup V] (D B : AddSubgroup V) (T : Finset V) : Prop :=
  (∀ t ∈ T, t ∈ D) ∧ ∀ β ∈ D, ∃! t, t ∈ T ∧ β - t ∈ B

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
