import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightLabelInvariantStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightTestBound
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolume
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveragedStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheorem
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNef
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9PropertiesStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT1Limit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DivSuppArithHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem chain_tower : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound →
    GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd →
    FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II →
    T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq →
    T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧
      T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  intro hFH hIn hZ1 hZ2 hAP hG II hII Ψ _ _ N _ T frob C C' rd Lval hC hC' hrd hfs hP hI1 hI2 hA1 hM1 hM2 hAN
    hI5 hI6 hI7 hI8 hP6 hPA hPF hVol hSL
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  have hI3 : T.I3 := _root_.GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs Ψ N T hA1 hM1 hM2 hAN
  have hT1 : T.T1 II := _root_.GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs II Ψ N T hP hI2 hI3
  have hW : T.ThmW II := _root_.GlobalTheory.CompanionTheory.Ar.Top.thmW_tower hIn.2.2.2.2.2.1 _root_.GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat GlobalTheory.CompanionTheory.Ar.Link.divSuppArith_holds hZ1 hZ2
    II hII Ψ N T hP hI1 hI2 hI3 hI5 hI6 hI7
  have hI9 : I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_I9_properties hFH hIn II hII Ψ N hN
  have hB : T.ThmB II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B hAP II Ψ N T (hhFl Ψ N II) hP hW hI8 hI9
  have he : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
    simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]
  have hAr := (_root_.GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image Ψ N hN).1
  rw [he] at hAr
  have hLab : LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_label_invariant II hII Ψ N hN hAr
  have hBA : T.ThmBA II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B_averaged II Ψ N T (hhFl Ψ N II) hB hPA hLab
  have hTest : HhTestBound T.j (hhFl Ψ N II) := _root_.GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl hG hIn II hII Ψ N T.j T.j_pos T.j_lt
  have hA0 : T.LowerBoundAtBase II (hhFl Ψ N II) frob (2 * (C + C') + 3) rd Lval :=
    GlobalTheory.T.test_height_bound II Ψ N T (hhFl Ψ N II) frob C C' rd Lval hC hC' hrd hP hI9 hPF hSL hTest
  have hK : (0 : ℝ) ≤ 2 * (C + C') + 3 := by linarith
  have hT2' := GlobalTheory.T.tower_T2 II Ψ N T (hhFl Ψ N II) frob (2 * (C + C') + 3) C' rd Lval hK hC' hrd hP hfs hI9 hP6
    hBA hPF hA0
  have hEq : 2 * (C + C') + 3 + C' + 2 = 2 * C + 3 * C' + 5 := by ring
  rw [hEq] at hT2'
  exact ⟨hT1, hB, hT2', _root_.GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq II Ψ N T _ rd Lval hP hVol hT2'⟩

end GlobalTheory.CompanionTheory.Ar.Top
