import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def betaYOf (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (j : ℕ) : GL (Fin (D.sp.Y j).rank) (EAf D) :=
  if h : j ≤ D.R.m then
    (show GL (Fin (Yc D j).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D) by
      unfold Yc; rw [Nat.min_eq_left h]) ▸ βY j
  else 1

def SDFrames (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  (∀ j, j < D.R.m → IsSDFrame (Yc D j) (βY j) (ΛY j) (D.host.g 0 * D.host.g 1)) ∧
    IsSDFrame D.sp.X' βX ΛX 1 ∧ (∀ i, IsSDFrame (Vc D i) (βV i) (ΛV i) 1) ∧
    ∀ i, IsSDFrame (Wc D i) (βW i) (ΛW i) 1

def IsHyperbolicFrameAt (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (j : ℕ) :
    Prop :=
  (∀ i < (D.R.m - 1 - j) / 2, ∀ l < (D.R.m - 1 - j) / 2,
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (ev j l)) = (if i = l then 1 else 0) ∧
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (e j l)) = 0 ∧ (D.sp.Y j).hT (vecY j (ev j i)) (vecY j (ev j l)) = 0) ∧
    ((D.R.m - 1 - j) % 2 = 1 →
      (D.sp.Y j).hT (vecY j (z j)) (vecY j (z j)) = -(D.sp.T : D.host.E) ∧
      ∀ i < (D.R.m - 1 - j) / 2,
        (D.sp.Y j).hT (vecY j (z j)) (vecY j (e j i)) = 0 ∧ (D.sp.Y j).hT (vecY j (z j)) (vecY j (ev j i)) = 0) ∧
    ∀ x : (D.sp.X j).V, ∀ i' < D.R.m - 1 - j,
      (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (adaptedVector e ev z j i')) = 0

open Classical in

def ColsAt (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E)
    (Pg : Finset (Pl D.host.E)) (PP : Pl D.host.E) (ei : AE D) (j : ℕ) : Prop :=
  (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i →
      ColAt j (βY j).val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) *
          (nfScal κ s j i * adaptedVector e ev z j i r)) ∧
    (∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
      XSpanAt j (βY j).val ei col)

theorem vecY_repr (j : ℕ) (v : (D.sp.Y j).V) : vecY (D := D) j ⇑((D.sp.Y j).frame.repr v) = v := by
  simp [vecY]

variable (D) in

def AdaptedVectorsExist : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E),
    ∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j

end Formalism.IndefR.Seed.Frm

end
