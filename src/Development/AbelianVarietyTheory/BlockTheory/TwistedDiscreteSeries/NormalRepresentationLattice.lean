import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def nfBasis (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embX c g * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)

theorem nfBasis_val (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : (nfBasis ϖ g e z).val =
    fromBlocks g.val (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp

theorem nfBasis_one (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : nfBasis ϖ 1 e z = normalBasis ϖ e z := by
  simp [nfBasis, normalBasis]

variable [ValuativeRel k]

def powInt (ϖ : kˣ) (e : ℤ) : Set k := {s | valuation k s ≤ valuation k ((ϖ ^ e : kˣ) : k)}

def topCoord (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : Fin c) : Set k :=
  {s | ∃ y ∈ Λ, (∀ l, i < l → y (Sum.inr l) = 0) ∧ y (Sum.inr i) = s}

def MeetsIn (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (L : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ y : n → k, Sum.elim y 0 ∈ Λ ↔ y ∈ L

def MapsLat {ι ι' : Type*} [Fintype ι'] (x : Matrix ι ι' k) (Λ' : Submodule 𝒪[k] (ι' → k))
    (Λ : Submodule 𝒪[k] (ι → k)) : Prop := ∀ v ∈ Λ', x *ᵥ v ∈ Λ

end Plain

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def NormalFormModN : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (h : GL (n ⊕ Fin c) k),
    ∃ u ∈ N k n c 1, ∃ (g : GL n k) (e : Fin c → ℤ) (z : n → k),
      latOf (u * h) = latOf (nfBasis ϖ g e z) ∧ MeetsIn (latOf h) (latOf g)

variable [MeasurableSpace k] [BorelSpace k]

variable {k}
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  (T : Chain k s X Z) (ϖ : kˣ) (ψ : AddChar k Circle) (ν : Measure k)

def IsNormalRep (j c : ℕ) (h : j + c = s) (g : GL (X j ⊕ Fin (c + 1)) k) : Prop :=
  ∃ (e : Fin (c + 1) → ℤ) (z : X j → k), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)

end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
