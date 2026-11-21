import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def IdE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def TrueE (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ ∃ w : World I l Z, IdE w.S.X

theorem TrueE.trueD {D : D7} (h : TrueE D) : TrueD D :=
  let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩

def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ Deg.DataNW D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def Row (E : D7 → ℝ → ℝ → Prop) (Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, 1 ≤ C ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (u : D.what₂.Word), TrueE D → E D L C' → HD D L C' Cl Cg cb Cu cT CT → Q D u L C

variable (E : D7 → ℝ → ℝ → Prop)

def RowDiag : Prop := Row E fun D u L C => SDiag D u L C

variable {E}

theorem Row.and {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} {Q' : ∀ D : D7, D.what₂.Word → Prop} (h : Row E Q)
    (h' : Row E fun D u _ _ => Q' D u) : Row E fun D u L C => Q D u L C ∧ Q' D u := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  let ⟨_, a', b', _, h'⟩ := h' Cg cb Cu cT CT h1 h2
  ⟨C, max a a', max b b', hC, fun C' Cl ha hb D L u hD hE hH =>
    ⟨h C' Cl (le_trans (le_max_left _ _) ha) (le_trans (le_max_left _ _) hb) D L u hD hE hH,
      h' C' Cl (le_trans (le_max_right _ _) ha) (le_trans (le_max_right _ _) hb) D L u hD hE hH⟩⟩

end GlobalTheory.Core.Rk

end
