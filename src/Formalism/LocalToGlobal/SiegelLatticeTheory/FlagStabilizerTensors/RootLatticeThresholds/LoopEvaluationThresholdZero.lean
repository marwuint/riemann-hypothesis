import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GammaFixedOfHypotheses
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ConcAt0 (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y

section TransportedAlt

theorem loop_evaluation_threshold_zero (hLC : PN.LoopCores) (hSub : PB.SubFamily) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio)
    (Cg cb Cw cT CT C0 A C₀ : ℝ) :
    ∃ C'₀ Cl₀ : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
      (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
      (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)),
      (∀ C : ℝ, C₀ ≤ C → OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A →
          Formalism.MainNotions.BridgeLemma.RowsND (At x hx i) (Yt x hx i u u') C ∧ Formalism.MainNotions.BridgeLemma.RowsDeg (At x hx i) (Yt x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (At x hx i) (Yt x hx i u u') C) →
      (OwnEv Fm fun C' Cl x i =>
        Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cw cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) →
      OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
        ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
          Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
          ((Cc x hx i).Y.tO u u').AbsConv →
          ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
          ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
  obtain ⟨C₃, _, HX⟩ := xiSizesC_of hS Cg cb Cw cT CT C0 A
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max C₀ C₃) (max CT 1) := ⟨_, rfl⟩
  have hCC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCT : CT ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hLC hSub C hC
  obtain ⟨a3, b3, HX'⟩ := HX C hCC₃
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 1 C0 := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  refine ⟨max a3 K₀, max b3 (max 4 (3 + 6 * Real.log (3 * A₀))), ?_⟩
  intro eps Fm C1 At Yt Cc HR hFo
  refine (OwnEv.and (HR C hCC₀) hFo).mono ?_
  rintro C' Cl x i ⟨H1, H2⟩ hC' hCl hx u u' hH hT hA
  have ha3 : a3 ≤ C' := le_trans (le_max_left _ _) hC'
  have hK₀ : K₀ ≤ C' := le_trans (le_max_right _ _) hC'
  have hb3 : b3 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl4 : 4 ≤ Cl := le_trans (le_max_of_le_right (le_max_left _ _)) hCl
  have hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl := le_trans (le_max_of_le_right (le_max_right _ _)) hCl
  obtain ⟨hn, hd, h1⟩ := H1 hx u u' hH
  have hFo' := H2 hH.1 u
  have hGP : GamPin (Cc x hx i).Y := gammaFixed_of_hypotheses (Cc x hx i).Y hH.1
  have hXiH := HX' C' Cl ha3 hb3 (Fm.D x i) (Fm.L x i) u u' hH
  have hP := params_at hH.1 (Cc x hx i).X u hCl4 hCT hC hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b (Fm.D x i) (Fm.L x i)
  have hb0 : (0 : ℝ) < (Fm.L x i).sc.b := by linarith
  have hk0 : (0 : ℝ) < (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < (Fm.D x i).R.k)
  have hg : 0 < ((Cc x hx i).X.B.g : ℝ) := by
    have h5 : (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Cc x hx i).X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ (Fm.D x i).host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0' : (0 : ℝ) ≤ C := by linarith
  have hGam : 0 ≤ GamS (Fm.D x i) (Fm.L x i) := by unfold GamS; exact (Real.exp_pos _).le
  have HS : ∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
      ClassLe ((Cc x hx i).Y.tO u u') (bigS ((Cc x hx i).Y.tO u u') s)
        (A₀ * rowS C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f s (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
          (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
          ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    intro s h2 hk
    have hX0 := xi_nonneg hXiH s h2 hk
    rw [hA₀]
    exact rowsSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      hH C hn hd s h2 hk (ndRow_nonneg hC0' hb0 hg hv hGam hX0) (degRow_nonneg hC0' hb0 hg hv hGam hX0)
  have H1' : ClassLe ((Cc x hx i).Y.tO u u') (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet)
      (A₀ * oneT C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
        (GamS (Fm.D x i) (Fm.L x i)) * ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    rw [hA₀]
    exact oneSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      C0 C hC0' h1
  obtain ⟨Al, NT', Gam, Xi, hAl, hP', hX', h6, hAmp⟩ :=
    loopsAmp_at hH hT hA hC hCT hK₀ hA₀1 hCl4 hClA hXiH HS H1'
  exact hJ _ _ _ _ _ ((Cc x hx i).Y.tO u u') (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f Al (Fm.L x i).sc.b
    ((Cc x hx i).X.B.g : ℝ) (Fm.D x i).host.v NT' Gam Xi (ddC (Cc x hx i).X (Cc x hx i).Y u u')
    hAl hP' hX' h6 (dd_nonneg hT u u') hA
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ hA.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

end TransportedAlt

end Formalism.L2.SG.LoopsTies
