import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]

def put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0

open Classical in

def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

end GlobalTheory.GamMul

end
