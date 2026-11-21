import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def idl (b : kˣ) : Submodule 𝒪[k] k := Submodule.span 𝒪[k] {(b : k)}

def monLat {n : Type} (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (b : ℕ → kˣ) :
    Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {v | (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, v (Sum.inr i) ∈ idl (b (i.val + 1))}
  add_mem' hv hw := ⟨L.add_mem hv.1 hw.1, fun i => (idl _).add_mem (hv.2 i) (hw.2 i)⟩
  zero_mem' := ⟨L.zero_mem, fun _ => (idl _).zero_mem⟩
  smul_mem' s _ hv := ⟨L.smul_mem s hv.1, fun i => (idl _).smul_mem s (hv.2 i)⟩

def frame (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (b : ℕ → kˣ) : GL (n ⊕ Fin c) k :=
  embA n ⟨Matrix.diagonal fun i : Fin c => (b (i.val + 1) : k),
    Matrix.diagonal fun i : Fin c => ((b (i.val + 1))⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
