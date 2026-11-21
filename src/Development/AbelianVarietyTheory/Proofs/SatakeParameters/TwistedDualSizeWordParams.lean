import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageWordSEtaM
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordNum : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨rfl, hg⟩ := hO
  generalize g 0 = τ at hg
  obtain rfl : g = letter τ ψ := funext hg
  have hsm := pageWord_S_eta_m L j ε τ ψ
  refine ⟨?_, ?_, ?_, hsm.1, hsm.2.1, rfl⟩
  · intro a
    obtain ⟨hsz, -, -, hth⟩ := _root_.GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord L C j ε τ ψ hR a
    rcases _root_.GlobalTheory.HTW.pageWord_thickOr L C j ε τ ψ hR a with h | h
    · exact Or.inl (hth.2 h)
    · refine Or.inr ?_
      have h' : (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) ≤ ((wHat D : ℕ) : ℤ) := by
        rw [hsz]; exact h
      exact_mod_cast h'
  · have h := bHat_add_etaHat_add_sHat_le_hPage L C hR
    exact h
  · exact (_root_.GlobalTheory.HTW.Rec.wMax_le_wB L).2

end GlobalTheory.HTW.Rec
