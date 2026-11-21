import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound

def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)

def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α

section Hecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def diagJ (n : ℕ) (ϖ : kˣ) (j : ℕ) : GL (Fin n) k :=
  diagT k (Fin n) fun i => if (i : ℕ) < j then ϖ else 1

def HeckeEigen (π : Representation ℂ (GL (Fin n) k) V) (v : V) (t : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)),
    (∀ g : GL (Fin n) k, (g : GL (Fin n) k ⧸ KO k (Fin n)) ∈ S ↔
      ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), g = a * t * b) ∧
    ∑ x ∈ S, π x.out v = c • v

end Hecke

def SatakeTrivialBoundHecke : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (v : V) (ϖ : kˣ) (α : Fin n → ℂˣ),
    IsUnitarisable π → v ≠ 0 → v ∈ fixed π (KO k (Fin n)) → valuation k (ϖ : k) = uniformizer k →
    (∀ j : ℕ, 1 ≤ j → j ≤ n → HeckeEigen π v (diagJ n ϖ j)
      ((((resCard k : ℝ) ^ ((j : ℝ) * ((n : ℝ) - j) / 2) : ℝ) : ℂ) *
        (Finset.univ.val.map fun i => (α i : ℂ)).esymm j)) →
      InTrivialRange (resCard k) α

section Basic₂

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
