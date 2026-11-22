import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThickStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨_root_.GlobalTheory.HTW.pageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := _root_.GlobalTheory.HTW.InertWord.inert_nothree_nonthick D.host τ φ hLw hφ h
    have hth := _root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR
    refine ⟨(_root_.GlobalTheory.signs_alternate_inert ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
