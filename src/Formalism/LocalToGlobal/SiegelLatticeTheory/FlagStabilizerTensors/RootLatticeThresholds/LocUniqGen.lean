import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec

section Gen

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem toUJ_eq {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε)
    (x : Formalism.REAL.UJ ε) (h : M = uMat x) : toUJ M hM = x := by
  apply Subtype.ext
  apply Units.ext
  change uMat (toUJ M hM) = uMat x
  rw [uMat_toUJ, h]

variable {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem gam_cond (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ UH (Hpk k r)) :
    (Qm e f wf z0 * m * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * m * B0) = Formalism.REAL.Jm ε := by
  have hm' : mᴴ * Hpk k r * m = Hpk k r := hm
  have key : (Qm e f wf z0 * m * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * m * B0)
      = B0ᴴ * (mᴴ * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * m) * B0 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [key, gramQ hF, hm', hCP.BHB]

def gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ UH (Hpk k r)) : Formalism.REAL.UJ ε :=
  toUJ _ (gam_cond hF hCP hm)

theorem cM_gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ UH (Hpk k r)) :
    (Matrix.of (cM (Qi ε e f wf z0) P0 (gam hF hCP m hm)) : Matrix _ _ ℂ) = m := by
  have h1 : uMat (gam hF hCP m hm) = Qm e f wf z0 * m * B0 := uMat_toUJ _ _
  change (Qi ε e f wf z0 * uMat (gam hF hCP m hm) * P0 : Matrix _ _ ℂ) = m
  rw [h1]
  calc Qi ε e f wf z0 * (Qm e f wf z0 * m * B0) * P0
      = (Qi ε e f wf z0 * Qm e f wf z0) * m * (B0 * P0) := by simp only [Matrix.mul_assoc]
    _ = m := by rw [Qi_mul_Qm hF, hCP.BP, Matrix.one_mul, Matrix.mul_one]

theorem gam_cM (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (x : Formalism.REAL.UJ ε)
    (hm : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r)) :
    gam hF hCP _ hm = x := by
  unfold gam
  apply toUJ_eq
  change Qm e f wf z0 * (Qi ε e f wf z0 * uMat x * P0) * B0 = uMat x
  calc Qm e f wf z0 * (Qi ε e f wf z0 * uMat x * P0) * B0
      = (Qm e f wf z0 * Qi ε e f wf z0) * uMat x * (P0 * B0) := by simp only [Matrix.mul_assoc]
    _ = uMat x := by rw [Qm_mul_Qi hF, hCP.PB, Matrix.one_mul, Matrix.mul_one]

def WB {V : Type} [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (W : Formalism.REAL.UJ ε → V)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : V :=
  if hm : m ∈ UH (Hpk k r) then W (gam hF hCP m hm) else 0

theorem WB_cM {V : Type} [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (W : Formalism.REAL.UJ ε → V)
    (x : Formalism.REAL.UJ ε) : WB hF hCP W (Matrix.of (cM (Qi ε e f wf z0) P0 x)) = W x := by
  have hmem : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r) := by
    have hx : (uMat x)ᴴ * Formalism.REAL.Jm ε * uMat x = Formalism.REAL.Jm ε := uMat_mem x
    have hQ : Qm e f wf z0 * Qi ε e f wf z0 = 1 := Qm_mul_Qi hF
    change (Qi ε e f wf z0 * uMat x * P0)ᴴ * Hpk k r * (Qi ε e f wf z0 * uMat x * P0) = Hpk k r
    calc (Qi ε e f wf z0 * uMat x * P0)ᴴ * Hpk k r * (Qi ε e f wf z0 * uMat x * P0)
        = P0ᴴ * ((uMat x)ᴴ * ((Qm e f wf z0 * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε *
            (Qm e f wf z0 * Qi ε e f wf z0)) * uMat x) * P0 := by
          rw [← gramQ hF]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P0ᴴ * Formalism.REAL.Jm ε * P0 := by
          rw [hQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hx]
      _ = Hpk k r := hCP.cay
  unfold WB
  rw [dif_pos hmem, gam_cM]

end Gen

section Trans

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem continuous_gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) :
    Continuous (fun p : UH (Hpk k r) => gam hF hCP p.1 p.2) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : ∀ p : UH (Hpk k r), (((gam hF hCP p.1 p.2 : Formalism.REAL.UJ ε) :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix _ _ ℂ)
          = Qm e f wf z0 * p.1 * B0 := fun p => uMat_toUJ _ _
    simp only [Function.comp_def, e]
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  · have hinv : ∀ p : UH (Hpk k r), (((((gam hF hCP p.1 p.2 : Formalism.REAL.UJ ε) :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ))⁻¹ :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix _ _ ℂ)
          = Formalism.REAL.Jm ε * (Qm e f wf z0 * p.1 * B0)ᴴ * Formalism.REAL.Jm ε := fun p => rfl
    refine Continuous.congr (f := fun p : UH (Hpk k r) =>
      Formalism.REAL.Jm ε * (Qm e f wf z0 * p.1 * B0)ᴴ * Formalism.REAL.Jm ε) ?_ ?_
    · exact (continuous_const.matrix_mul
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).matrix_conjTranspose).matrix_mul
        continuous_const
    · intro p
      exact (hinv p).symm

theorem WB_continuousOn {V : Type} [TopologicalSpace V] [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    {W : Formalism.REAL.UJ ε → V} (hW : Continuous W) : ContinuousOn (WB hF hCP W) (UH (Hpk k r)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hr : ∀ p : UH (Hpk k r), WB hF hCP W p.1 = W (gam hF hCP p.1 p.2) := by
    intro p
    unfold WB
    rw [dif_pos p.2]
  have hc : Continuous (fun p : UH (Hpk k r) => WB hF hCP W p.1) := by
    have hf : (fun p : UH (Hpk k r) => WB hF hCP W p.1) = fun p => W (gam hF hCP p.1 p.2) := funext hr
    rw [hf]
    exact hW.comp (continuous_gam hF hCP)
  exact hc

end Trans

section TransEq

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem cM_eq_of (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hm : m ∈ UH (Hpk k r)) : m = (Matrix.of (cM (Qi ε e f wf z0) P0 (gam hF hCP m hm)) : Matrix _ _ ℂ) := (cM_gam hF hCP m hm).symm

theorem WB_equiv (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) {zB z : Fin (2 * r + k + 1) → ℂ}
    (hz : (Qm e f wf z0) *ᵥ zB = z) {gg : ℕ} (hgg : 0 < gg) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} {W : Formalism.REAL.UJ ε → V}
    (hWe : ∀ s x : Formalism.REAL.UJ ε, ∀ h ∈ UWset k r zB, ∀ m ∈ Nset k r,
      Qi ε e f wf z0 * uMat s * Qm e f wf z0 = h * m →
      W (s * x) = psiR ε gg e f z (uMat s) • piB ε e f wf z0 πl h (W x)) :
    IsSPsiEquiv zB (Formalism.QuantumDeterminants.psi k r zB ((4 * Real.pi / gg : ℝ) : ℂ)) (piB ε e f wf z0 πl) (WB hF hCP W) := by
  intro h hh m hm g hg
  have hhm : h * m ∈ UH (Hpk k r) := mem_UH_mul hh.1 hm.1
  set s : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * (h * m) * Qi ε e f wf z0) (conjQ_UJ hF hhm) with hs
  set x := gam hF hCP g hg with hx
  have hus : uMat s = Qm e f wf z0 * (h * m) * Qi ε e f wf z0 := uMat_toUJ _ _
  have hsQ : Qi ε e f wf z0 * uMat s * Qm e f wf z0 = h * m := by rw [hus]; exact Qi_Qm_conj hF _
  have hsx : h * m * g = (Matrix.of (cM (Qi ε e f wf z0) P0 (s * x)) : Matrix _ _ ℂ) := by
    have hg' := cM_gam hF hCP g hg
    show h * m * g = Qi ε e f wf z0 * uMat (s * x) * P0
    rw [Formalism.L2.SG.WuDecayPf.uMat_mul', hus]
    conv_lhs => rw [← hg']
    show h * m * (Qi ε e f wf z0 * uMat x * P0) = _
    simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
  rw [hsx, WB_cM, cM_eq_of hF hCP g hg, WB_cM, hWe s x h hh m hm hsQ]
  congr 1
  rw [← psi_conj hF hz hgg (uMat s), hsQ, psiGen_UW_mul _ hh, Formalism.L2.SG.LitS.psi_eq_psiGen]

end TransEq

section TransRep

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem WB_reprod (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {W : Formalism.REAL.UJ ε → V}
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x) :
    ∀ x' ∈ UH (Hpk k r),
      Integrable (fun g : Mt k r => eFun ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w
          (Matrix.of g) • WB hF hCP W (x' * Matrix.of g)) ((Formalism.REAL.muG ε).map (cM B0 P0)) ∧
      rconv ((Formalism.REAL.muG ε).map (cM B0 P0)) (eFun ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w)
        (WB hF hCP W) x' = WB hF hCP W x' := by
  intro x' hx'
  set x := gam hF hCP x' hx' with hxdef
  have hx'eq : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) = x' := cM_gam hF hCP x' hx'
  obtain ⟨hint, hval⟩ := hWr x
  have embG := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have hfd := fdegH_map hCP σ w
  have hσg : ∀ g : Formalism.REAL.UJ ε, σ (P0 * (Matrix.of (cM B0 P0 g) : Matrix _ _ ℂ) * B0) = σ (uMat g) := by
    intro g
    show σ (P0 * (B0 * uMat g * P0) * B0) = σ (uMat g)
    congr 1; simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]; rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hprod : ∀ g : Formalism.REAL.UJ ε, (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) *
      Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi ε e f wf z0) P0 (x * g)) := fun g => cMprod hCP _ x g
  have hpt : ∀ g : Formalism.REAL.UJ ε, eFun ((Formalism.REAL.muG ε).map (cM B0 P0))
      (fun M => σ (P0 * M * B0)) w (Matrix.of (cM B0 P0 g)) • WB hF hCP W (x' * Matrix.of (cM B0 P0 g)) =
      (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g) := by
    intro g
    simp only [eFun]
    rw [hfd, hσg, ← hx'eq, hprod, WB_cM]
  refine ⟨?_, ?_⟩
  · exact embG.integrable_map_iff.mpr (hint.congr (ae_of_all _ fun g => (hpt g).symm))
  · unfold rconv
    rw [embG.integral_map, integral_congr_ae (ae_of_all _ hpt), hval, ← hx'eq, WB_cM]

end TransRep

section Main

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

variable {k r : ℕ}

theorem isHaarOn_smul {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : IsHaarOn S μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) : IsHaarOn S (c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : c • μ = c.toNNReal • μ := by
      rw [ENNReal.smul_def, ENNReal.coe_toNNReal hct]
    rw [this]
    infer_instance
  · intro h0
    apply h2
    rw [← Measure.measure_univ_eq_zero] at h0 ⊢
    rw [Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc0
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]

end Main

section Inst

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

theorem lowGap_of_gapHyp (D : Formalism.BasicNotions.D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) :
    LowGapGe (16 * (D.R.r : ℝ) ^ 19) D.R.rS (Formalism.MainNotions.b48 D τ) := by
  obtain ⟨-, hgap⟩ := hG
  have hm := Formalism.MainNotions.two_rS_add_two D
  intro j hj
  have hj' : (Fin.cast hm j).1 + 1 < D.R.m := by simp; omega
  have hg := hgap τ (Fin.cast hm j) hj'
  have : Formalism.MainNotions.b48 D τ ⟨j.val + 1, hj⟩ - Formalism.MainNotions.b48 D τ j =
      (((D.hc τ).b ⟨(Fin.cast hm j).1 + 1, hj'⟩ - (D.hc τ).b (Fin.cast hm j) : ℚ) : ℝ) := by
    simp only [Formalism.MainNotions.b48]; push_cast; rfl
  rw [this]
  exact_mod_cast hg

theorem big_real (x y N : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : N = 2 * x + y + 1) (hN1 : 1801 ≤ N) :
    120 * N ^ 3 ≤ 16 * N ^ 19 ∧
    2 * (2 * (x ^ 2 + x + 1)) * ((2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)) +
      4 * (y + x) * (x + 1) + 3 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) ∧
    9 * (x + 1) * N ^ 2 + 3 * (4 * (y + x) * (x + 1)) + 3 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) := by
  have hN0 : 0 ≤ N := by linarith
  have hN1' : 1 ≤ N := by linarith
  have hxN : x ≤ N := by linarith
  have hyN : y ≤ N := by linarith
  have hx1 : x + 1 ≤ N := by linarith
  have hyx : y + x ≤ N := by linarith
  have hNN : N ≤ N * N := le_mul_of_one_le_right hN0 hN1'
  have eN2 : N ^ 2 = N * N := by ring
  have hNN2 : 1801 * N ≤ N * N := mul_le_mul_of_nonneg_right hN1 hN0
  have hs0 : 0 < Real.sqrt (2 * (x + 1)) := Real.sqrt_pos.mpr (by linarith)
  have hsN : Real.sqrt (2 * (x + 1)) ≤ N :=
    calc Real.sqrt (2 * (x + 1)) ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by rw [eN2]; linarith)
      _ = N := Real.sqrt_sq hN0
  have h12 : 1 ≤ N ^ 12 := one_le_pow₀ hN1'
  have h13 : 150 ≤ N ^ 13 := by
    calc (150 : ℝ) ≤ N * 1 := by linarith
      _ ≤ N * N ^ 12 := mul_le_mul_of_nonneg_left h12 hN0
      _ = N ^ 13 := by ring
  have h2 : 0 ≤ N ^ 2 := pow_nonneg hN0 2
  have h3 : 1 ≤ N ^ 3 := one_le_pow₀ hN1'
  have h3' : 0 ≤ N ^ 3 := pow_nonneg hN0 3
  have h5 : 1 ≤ N ^ 5 := one_le_pow₀ hN1'
  have h6 : 0 ≤ N ^ 6 := pow_nonneg hN0 6
  have h613 : 150 * N ^ 6 ≤ N ^ 13 * N ^ 6 := mul_le_mul_of_nonneg_right h13 h6
  have e19 : N ^ 13 * N ^ 6 = N ^ 19 := by ring
  have hR : 300 * N ^ 5 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) := by
    rw [le_div_iff₀ (by linarith)]
    have hm : 300 * N ^ 5 * (8 * Real.sqrt (2 * (x + 1))) ≤ 300 * N ^ 5 * (8 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e1 : 300 * N ^ 5 * (8 * N) = 2400 * N ^ 6 := by ring
    linarith
  have hxx : x * x ≤ N * N := mul_le_mul hxN hxN hx hN0
  have hxy : x * y ≤ N * N := mul_le_mul hxN hyN hy hN0
  have hxy0 : 0 ≤ x * y := mul_nonneg hx hy
  have hxx0 : 0 ≤ x * x := mul_nonneg hx hx
  have hC1 : (y + x) * (x + 1) ≤ N * N := mul_le_mul hyx hx1 (by linarith) hN0
  have hC10 : 0 ≤ (y + x) * (x + 1) := mul_nonneg (by linarith) (by linarith)
  have hA : 2 * (2 * (x ^ 2 + x + 1)) ≤ 12 * N ^ 2 := by
    have ex : x ^ 2 = x * x := by ring
    rw [ex, eN2]
    linarith
  have hA0 : 0 ≤ 2 * (2 * (x ^ 2 + x + 1)) := by
    have ex : x ^ 2 = x * x := by ring
    rw [ex]
    linarith
  have eB : x * (x - 1) + 2 * x * (y + 1) + x ^ 2 = 2 * (x * x) + x + 2 * (x * y) := by ring
  have hB1 : x * (x - 1) + 2 * x * (y + 1) + x ^ 2 ≤ 6 * N ^ 2 := by
    rw [eB, eN2]
    linarith
  have hB0 : 0 ≤ x * (x - 1) + 2 * x * (y + 1) + x ^ 2 := by
    rw [eB]
    linarith
  have eC : 4 * (y + x) * (x + 1) = 4 * ((y + x) * (x + 1)) := by ring
  have hC : 4 * (y + x) * (x + 1) ≤ 4 * N ^ 2 := by
    rw [eC, eN2]
    linarith
  have hC0 : 0 ≤ 4 * (y + x) * (x + 1) := by
    rw [eC]
    linarith
  have hD : 2 * x + y ≤ N := by linarith
  have hD0 : 0 ≤ 2 * x + y := by linarith
  have hDB := mul_le_mul hD hB1 hB0 hN0
  have hDB0 := mul_nonneg hD0 hB0
  have h23 : N ^ 2 ≤ N ^ 2 * N := le_mul_of_one_le_right h2 hN1'
  have e3 : N * (6 * N ^ 2) = 6 * N ^ 3 := by ring
  have e3' : N ^ 2 * N = N ^ 3 := by ring
  have hB : (2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)
      ≤ 10 * N ^ 3 := by linarith
  have hB0' : 0 ≤ (2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1) := by
    linarith
  have hAB := mul_le_mul hA hB hB0' (by linarith)
  have e5 : 12 * N ^ 2 * (10 * N ^ 3) = 120 * N ^ 5 := by ring
  have h25 : N ^ 2 ≤ N ^ 2 * N ^ 3 := le_mul_of_one_le_right h2 h3
  have e5' : N ^ 2 * N ^ 3 = N ^ 5 := by ring
  have h35 : N ^ 3 ≤ N ^ 3 * N ^ 2 := le_mul_of_one_le_right h3' (one_le_pow₀ hN1')
  have e5'' : N ^ 3 * N ^ 2 = N ^ 5 := by ring
  have h36 : N ^ 3 ≤ N ^ 3 * N ^ 3 := le_mul_of_one_le_right h3' h3
  have e6 : N ^ 3 * N ^ 3 = N ^ 6 := by ring
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · have hAB' : 2 * (2 * (x ^ 2 + x + 1)) *
        ((2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)) ≤ 120 * N ^ 5 := by
      linarith
    linarith
  · have h9 : (x + 1) * N ^ 2 ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hx1 h2
    have e9 : N * N ^ 2 = N ^ 3 := by ring
    have e9' : 9 * (x + 1) * N ^ 2 = 9 * ((x + 1) * N ^ 2) := by ring
    rw [e9']
    linarith

theorem gapOK_of_big (k r : ℕ) (hk : 1 ≤ k) (hN : 1801 ≤ 2 * r + k + 1) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (16 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19) := by
  have hb := big_real (r : ℝ) (k : ℝ) ((2 * r + k + 1 : ℕ) : ℝ) (Nat.cast_nonneg r) (Nat.cast_nonneg k)
    (by push_cast; ring) (by exact_mod_cast hN)
  refine ⟨hk, hb.1, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.aOf Formalism.FourierDecayAlt.ThreeDimData.dN
    have e1 : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e1]
    have := hb.2.1
    convert this using 2 <;> ring
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.aOf
    have := hb.2.2
    convert this using 2 <;> ring

end Inst

end Formalism.L2.SG.Pf.WuDec
