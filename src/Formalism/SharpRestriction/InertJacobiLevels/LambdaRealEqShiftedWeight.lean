import Formalism.SharpRestriction.InertJacobiLevels.TiesLat

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Build

variable {D : D7} (hT : GatTies D) (L : SizeData₂ D)

variable {L} (X : G.Inst D L)

structure PosHyp where
  vOf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    G.HH D → Fin (D.gat u w hg).P.nV
  inj : ∀ u w hg, Set.InjOn (vOf u w hg) (G.reps X (D.what₂.places.resChar w))
  n_eq : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w),
    (D.gat u w hg).P.n' (vOf u w hg t0) = addOrderOf (G.hP D (D.what₂.places.resChar w))
  pos : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w), ∀ s : Fin ((D.gat u w hg).P.n' (vOf u w hg t0)),
    ((D.eTau (hT.gat_pos u w hg ⟨vOf u w hg t0, s⟩) : D.R.Psi) : D.R.GG) =
      D.R.tau1 (t0 + s.val • G.hP D (D.what₂.places.resChar w))
  r_eq : ∀ u w hg, (D.gat u w hg).P.r =
    (if ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k then G.rG L.sc else 1)

end Build

end Formalism.MainNotions.Inhab

end
