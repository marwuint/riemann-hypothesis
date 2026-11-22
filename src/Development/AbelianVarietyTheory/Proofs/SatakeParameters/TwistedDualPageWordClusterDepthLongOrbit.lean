import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeastPowerDepthSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_hypA_depth_of_long_orbit {D : D7} (L : SizeData₂ D) (hP : ParameterChoice' D L) (C : ℝ)
    (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ) (hR : Roomy L C) (hl : 11 ≤ l)
    (hlA : (l : ℝ) < LevelStarExponents.lA L) (ho : 4 * D.host.Lw < orderOf φ.2) :
    (pageWord L j ε τ φ).HypA (depth L l) := by
  obtain ⟨-, hLw, h2⟩ := _root_.GlobalTheory.depth_spec L hP l hl
  have h1 : 1 ≤ depth L l := le_trans (by norm_num) (h2 hlA)
  obtain ⟨hcl, hn⟩ := _root_.GlobalTheory.long_clusters D.host τ φ (depth L l) ho h1 hLw
  have hbox := _root_.GlobalTheory.HTW.pageWord_box L C j ε τ φ hR
  have hth : (pageWord L j ε τ φ).thick = fun i : ZMod (orderOf φ) => Thick D.host (letter τ φ i) :=
    funext fun i => propext (_root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR i)
  have hpar := GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L 40 C (depth L l) hR (by norm_num) (by linarith [hR.1]) hLw
  refine ⟨fun i => ?_, h1, hn, fun _ => ?_, ?_⟩
  · have := hbox.2.2.2.2.2 i
    have h0 : (0 : ℤ) ≤ ((pageWord L j ε τ φ).η : ℤ) := Int.natCast_nonneg _
    linarith
  · show 40 * (depth L l + 1) * (wHat D + sHat L + etaHat L + 1) ≤ bHat L
    exact_mod_cast hpar
  · rw [hth]; exact hcl

end GlobalTheory.HTW
