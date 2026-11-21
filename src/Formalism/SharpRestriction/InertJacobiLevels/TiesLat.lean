import Formalism.SharpRestriction.InertJacobiLevels.TieTTwValsOfMem

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem tau_top_places_iff (D : D7) (t : G.HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← plGG_false, plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

structure LatHyp {D : D7} (hT : GatTies D) {L : SizeData₂ D} (X : G.Inst D L) where
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
  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L
  wZ : D.what₂.Tau → ℕ → ℤ
  wZ_eq : ∀ τ, ∀ j ∈ SizeData₂.lifts D, (wZ τ j : ℝ) = wj D j τ - G.kaJ D j
  wZ_mono : ∀ τ j, 1 ≤ j → wZ τ j ≤ wZ τ (j + 1)
  base_top : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (t : D.host.TT),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 t →
    (D.gat u w hg).P.lam0 v s 0 = L.aT t ∧ (D.gat u w hg).P.lam0 v s (Fin.last _) = -L.bT t ∧
      ∀ i : Fin ((D.gat u w hg).P.m + 1), 0 < i.val → i.val < (D.gat u w hg).P.m →
        |(D.gat u w hg).P.lam0 v s i| ≤ c
  base_off : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
    ∀ i, |(D.gat u w hg).P.lam0 v s i| ≤ c
  wZ_ge : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    max (c : ℤ) (-((D.gat u w hg).P.lam0 v s (Fin.last _))) ≤ wZ (hT.gat_pos u w hg ⟨v, s⟩) 1

namespace LatHyp

end LatHyp

end Formalism.MainNotions.Inhab

end
