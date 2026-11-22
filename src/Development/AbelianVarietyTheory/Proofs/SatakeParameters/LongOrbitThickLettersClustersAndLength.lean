import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := _root_.GlobalTheory.HTW.LongWindow.main H τ φ h4
  refine ⟨_root_.GlobalTheory.HTW.winClusters _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
