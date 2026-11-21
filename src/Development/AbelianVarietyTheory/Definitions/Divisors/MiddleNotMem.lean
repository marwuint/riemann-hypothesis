import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

end GlobalTheory.FunObj.UnfModel
