import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def rankAll : ℕ := Module.finrank D.what₂.LL (LT.Vl D u 0)

def lengthN_vw (w : D.what₂.places.Pl) : ℕ∞ :=
  Module.length (LT.Ow D w) (↥(LT.Sram D u w) ⧸ (LT.Nlam D u w).comap (LT.Sram D u w).subtype)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

def topSize (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : ℝ :=
  ((D.fm u).aTop ((D.fm u).tauOf w v) : ℝ) / (D.R.k : ℝ) + 2 * (Wtau D u ((D.fm u).tauOf w v) : ℝ)

def boundQuoted_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
    (topSize D u w v + (D.R.k : ℝ) + ((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ))

def IndexAtLevelKnown : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    LT.Nlam D u w ≤ LT.Sram D u w ∧
    ∃ l : ℕ, lengthN_vw D u w = (l : ℕ∞) ∧
      (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * boundQuoted_vp D u w

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
