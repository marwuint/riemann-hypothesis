import Mathlib
import Formalism.DropLevelBounds.Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WtAddSingle
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitCase

variable {C : Type} [Field C] {σ κ : Type}

def mult (O : Subring C) (l : ℕ) : AddSubgroup C :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft (l : C))

lemma mem_mult {O : Subring C} {l : ℕ} {x : C} : x ∈ mult O l ↔ ∃ o ∈ O, (l : C) * o = x :=
  Iff.rfl

lemma jetAt0_eq_sum (P : MvPolynomial σ C) (G : MvPowerSeries σ C) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  simp

end GlobalTheory.UnitCase
