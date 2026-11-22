import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdGen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdSm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
import Formalism.HermitianCurvature.BesselNonvanishingReduction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄

def MeasSideP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → PI.UpqRep.IsHCTypeW k r z u π →
    PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN →
    Cv.MeasF z π μW μN

theorem thresholds {k r : ℕ} {a : ℝ}
    (ha : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) + Formalism.FourierDecayAlt.ThreeDimData.AG k r + 3 ≤ a) :
    1 ≤ a ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r < (a - 1) / 2 ∧ Formalism.FourierDecayAlt.ThreeDimData.AS k r < (a - 1) / 2 := by
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    positivity
  have hdN : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.dN
    nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hAS : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    exact mul_nonneg (Nat.cast_nonneg _) hdN
  have hM : 2 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp
    nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hMS : 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) :=
    mul_le_mul_of_nonneg_right hM (by linarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def DecInfU (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v0 : H, IsKFinHpk (k := k) (r := r) σ v0 → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
      ‖⟪v0, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum *
        Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

theorem decBd_of_decInfU {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (hI : DecInfU σ a) {v0 w : H}
    (hv0 : IsKFinHpk (k := k) (r := r) σ v0) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    DecBd σ (a - 1) v0 w := by
  obtain ⟨C, Ws, -, hC⟩ := hI v0 hv0
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum, fun x hx => ?_⟩
  have h1 := hC w hw x hx
  rwa [show (1 - a) = -(a - 1) by ring] at h1

theorem normId_gen_bd {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] {σ : Mx k r → (H →L[ℂ] H)}
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} (hds : IsDSHpk k r ε lam σ)
    (hHaar : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muSof μW μN) ν)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {u v : H} (hu : u ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (huv : DecBd σ b v u) (hvv : DecBd σ b v v)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(b / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN))
    (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    (⟪ξ, be z c π μW μN σ v v ξ⟫_ℂ).im = 0 := by
  have : SFinite μG := sfinite_haar hHaar
  obtain ⟨C, hC⟩ := huv
  obtain ⟨C', hC'⟩ := hvv
  have hI : ∀ x ∈ UH (Hpk k r), Integrable (beF z c π σ (σ x u) v) (μW.prod μN) :=
    fun x hx => int_beF_of_bd hds hGr hPi hM hb (bd_shift hSg hb hC hx) hSS
  have hIv : Integrable (beF z c π σ v v) (μW.prod μN) := int_beF_of_bd hds hGr hPi hM hb hC' hSS
  have hD := dInt_of_bd hds hGr hHaar hM.1 hb hC hGg hSS
  exact normId_gen hds hHaar hq hGr hSg hPi hPs hM hS hu hI hIv hD ξ

theorem re_inner_swap (B : Wp →L[ℂ] Wp) (ξ : Wp) : (⟪B ξ, ξ⟫_ℂ).re = (⟪ξ, B ξ⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

end PI.WBL.NIS
