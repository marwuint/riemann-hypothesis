import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective

noncomputable section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.LeafTerm

variable {C : Type} [Field C]

section Chain

variable {Z I J : Type} [Fintype I]

variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}

def Adapted (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i → X.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))

variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}

theorem Adapted.good (h : Adapted S D a i) {c : I} (hc : D.good c) :
    X.Good (X.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  refine ⟨S.curve c, fun x => ?_⟩
  have := h.2.2.2.1 c 1 x le_rfl
  simpa [D.al_one c hc, Sys.al] using this

end Chain

end GlobalTheory.LeafTerm
