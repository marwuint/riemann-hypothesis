import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.HolCuspLevDeltaNeBot

noncomputable section

open GlobalTheory.SmGL GlobalTheory.TfJl ValuativeRel Matrix

namespace GlobalTheory.IwFn

section Lin

variable {G : Type} [Group G] {U : Subgroup G}

def hLin {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → HeckeFn U) : HeckeFn U where
  toFun g := ∑ i ∈ s, c i * (f i).toFun g
  left u hu g := by simp only [(f _).left u hu]
  right u hu g := by simp only [(f _).right u hu]
  fin := by
    refine (s.finite_toSet.biUnion fun i _ => (f i).fin).subset fun q hq => ?_
    obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact Set.mem_iUnion₂.2 ⟨i, hi, right_ne_zero_of_mul h⟩

theorem hLin_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → HeckeFn U) (g : G) :
    (hLin s c f).toFun g = ∑ i ∈ s, c i * (f i).toFun g := rfl

end Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a : ℕ}

def sList (S : Finset (Fin a)) : List (Fin a) := (List.finRange a).filter (· ∈ S)

def cyc (S : Finset (Fin a)) : Equiv.Perm (Fin a) := (sList S).formPerm

def dEnt (ϖ : kˣ) (S : Finset (Fin a)) (c : Fin a) : kˣ := if (sList S).head? = some c then ϖ else 1

def wS (ϖ : kˣ) (S : Finset (Fin a)) : GL (Fin a) k :=
  GeneralLinearGroup.mkOfDetNeZero ((cyc S).permMatrix k * diagonal fun c => (dEnt k ϖ S c : k)) (by
    rw [det_mul, det_permutation, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun c _ => Units.ne_zero _)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (cyc S)) with h | h <;> simp [h])

def phiS (ϖ : kˣ) (S : Finset (Fin a)) : HeckeFn (iwahori k (Fin a)) :=
  HeckeFn.dc (IwahoriOnto.isOpen_iwahori k (Fin a)) (IwahoriOnto.isCompact_iwahori k (Fin a)) (wS k ϖ S)

end GlobalTheory.IwFn
