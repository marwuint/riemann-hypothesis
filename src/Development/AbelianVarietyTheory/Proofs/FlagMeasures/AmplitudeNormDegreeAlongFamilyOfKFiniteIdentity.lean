import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Mathlib
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.AmpFamGap

theorem cellConv : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.CC.cell_convergence

theorem amplitudeNormDegree_along_family_of_kFiniteIdentity : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro hH hA Cg cb Cu cT CT C0 C1
  refine ⟨1000, fun eps Fm hC' hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := _root_.GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH hA cellConv Cg cb Cu cT CT C0 C1 Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i hZ => ?_⟩
  obtain ⟨-, hm0, -, -, hrd, -⟩ := hx0 x hx i
  have hm2 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have := (Fm.D x i).R.two_le_m
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.m)
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hm0⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hZ

theorem amplitudeNormDegree_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro _ hH _
  exact amplitudeNormDegree_along_family_of_kFiniteIdentity hH (_root_.GlobalTheory.AmpOrbGap.ampKF hH)

end GlobalTheory.AmpFamGap
