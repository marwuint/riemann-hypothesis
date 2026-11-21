import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

end LateralTheory.E.CorePf

end
