import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMass

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

open scoped Classical in

theorem lintegral_rmul_of_measurable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ≥0∞)
    (hF : Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)))
    (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, F (Matrix.of x * g) ∂νq = ∫⁻ x, F (Matrix.of x) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hF (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => hval x hx)))
  exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem norm_sq_sqrt_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {t d : ℝ} (ht : 0 ≤ t)
    (hd : 0 ≤ d) (v : Wp) : ‖((Real.sqrt t * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hd]
  ring

open scoped Classical in

theorem measurable_piecewise_mass {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (hφm : Measurable φ) (d : ℝ) (B : Mx k r → Wp) (hB : ContinuousOn B (GG k r)) :
    Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0)) := by
  classical
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hL : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) A :=
    continuousOn_pi.2 fun a => GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a
  have hLm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a)
      (fun _ => (0 : Fin (r + 1) → ℝ))) :=
    hL.measurable_piecewise continuousOn_const hAm
  have hBc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) A :=
    continuousOn_const.mul (hB.norm.pow 2)
  have hBm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ))) :=
    hBc.measurable_piecewise continuousOn_const hAm
  have heq : A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0) =
      A.indicator (fun x => ENNReal.ofReal (φ (A.piecewise
        (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) (fun _ => (0 : Fin (r + 1) → ℝ)) x)) *
        ENNReal.ofReal (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ)) x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, Set.indicator, hx]
    · simp [Set.piecewise, Set.indicator, hx]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp (hφm.comp hLm)).mul (ENNReal.measurable_ofReal.comp hBm)).indicator hAm

end prelim

end GlobalTheory.LowTypeMass
