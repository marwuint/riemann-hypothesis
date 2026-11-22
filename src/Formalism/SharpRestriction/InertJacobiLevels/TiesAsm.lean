import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

abbrev KapI : Type := ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ

structure LatIn (D : D7) where
  Vram : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn
  len : D.what₂.Word → D.what₂.places.Pl → ℚ

structure TieHyp {D : D7} (gatT : GatTies D) (L0 : SizeData₂ D) (kapI : KapI) (ep : ℕ → ℕ) where

  hw : 1 ≤ L0.sc.w'' D.R.n

  hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i))

  hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0

  htw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ L0.supp

  pos : PosHyp gatT (instW L0 kapI ep)

  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L0
  hcl : L0.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c

  hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
    |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c

  hw1 : ∀ τ, (c : ℝ) ≤ wj D 1 τ - G.kaJ D 1

namespace TieHyp

variable {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ} (H : TieHyp gatT L0 kapI ep)
  (K : G.Consts) (Cr : ℝ) (Λ : LatIn D)

def L : SizeData₂ D := tieL L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

end TieHyp

end Formalism.MainNotions.Inhab

end
