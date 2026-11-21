import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.PrincipalHermitianLattice

noncomputable section

namespace Formalism.BasicNotions

open scoped BigOperators

namespace DV

def eQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (D.hc τ).e ⟨j - 1, by omega⟩ else 0

def sigPar (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k - 1 then (D.hc τ).v ⟨i, h⟩
  else if hb : i - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i - (D.R.k - 1), hb⟩ else 0

def aPlusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  sigPar D τ i + eQ D j τ - ((D.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((D.R.k : ℚ) + j - 1) - ((D.R.m : ℚ) - j)) / 2

def aMinusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℚ :=
  (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) - eQ D j τ - ((D.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def aPlus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((aPlusQ D j τ i : ℚ) : ℝ)

def aMinus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℝ := ((aMinusQ D j τ c : ℚ) : ℝ)

def KapDef (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
    (∀ i : Fin (D.R.sigW j).1, (D.what₂.kaBig j τ i : ℚ) = aPlusQ D j τ i) ∧
    (∀ c : Fin (D.R.sigW j).2, (D.what₂.kaSmall j τ c : ℚ) = -aMinusQ D j τ c)

theorem eQ_cast (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ((eQ D j τ : ℚ) : ℝ) = wSz D j τ := by
  unfold eQ wSz
  split_ifs <;> simp

theorem eQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ∃ z : ℤ, eQ D j τ = z := by
  unfold eQ
  split_ifs
  · exact (D.hc τ).e_int _
  · exact ⟨0, by simp⟩

theorem sigPar_int (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, sigPar D τ i = z := by
  unfold sigPar
  split_ifs
  · exact (D.hc τ).v_int _
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i - (D.R.k - 1), by assumption⟩
    exact ⟨-z, by rw [hz]; simp⟩
  · exact ⟨0, by simp⟩

theorem nV_cast (R : Ranks) : (R.nV : ℚ) = (R.k : ℚ) + R.m - 1 + R.t := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.nV Ranks.r
  push_cast [Nat.cast_sub h]
  ring

theorem aPlusQ_eq (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) :
    aPlusQ D j τ i = sigPar D τ i + eQ D j τ - ((D.R.k : ℚ) + j - 1 - 1 - i) - ((D.R.t : ℚ) + 1) / 2 := by
  unfold aPlusQ
  rw [nV_cast]
  ring

theorem aPlusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, aPlusQ D j τ i = z := by
  obtain ⟨a, ha⟩ := sigPar_int D τ i
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  refine ⟨a + b - ((D.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩
  rw [aPlusQ_eq, ha, hb, hs]
  push_cast
  ring

theorem aMinusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ∃ z : ℤ, aMinusQ D j τ c = z := by
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  have h1 : ∃ a : ℤ, (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ) := by
    split_ifs
    · exact (D.hc τ).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := h1
  refine ⟨a - b - (s + 1 + c), ?_⟩
  unfold aMinusQ
  rw [ha, hb, hs]
  push_cast
  ring

theorem aPlusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aPlusQ D j τ (D.R.k + j - 1 - 1) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hi : ¬ (D.R.k + j - 1 - 1 < D.R.k - 1) := by omega
  have hb : D.R.k + j - 1 - 1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : D.R.k + j - 1 - 1 - (D.R.k - 1) = j - 1 := by omega
  have hc : ((D.R.k + j - 1 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : D.R.k + j - 1 - 1 = D.R.k + j - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hg := (D.hc τ).gap_be ⟨j - 1, by omega⟩
  rw [aPlusQ_eq, hc]
  unfold sigPar eQ
  rw [dif_neg hi, dif_pos hb, dif_pos ⟨h1, h2⟩]
  have : (⟨D.R.k + j - 1 - 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext hidx
  rw [this]
  linarith

theorem aMinusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aMinusQ D j τ 0 := by
  have hg := (D.hc τ).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < D.R.m; omega)
  have hidx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j + 0, by omega⟩ := Fin.ext (by show j - 1 + 1 = j + 0; omega)
  unfold aMinusQ eQ
  rw [dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩]
  rw [hidx] at hg
  push_cast
  linarith

theorem exists_blocks (D : D7) :
    ∃ (kb : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).1 → ℤ) (ks : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).2 → ℤ),
      ∀ j τ, (∀ i, (kb j τ i : ℚ) = aPlusQ D j τ i) ∧ (∀ c, (ks j τ c : ℚ) = -aMinusQ D j τ c) :=
  ⟨fun j τ i => (aPlusQ_int D j τ i).choose, fun j τ c => -(aMinusQ_int D j τ c).choose,
    fun j τ => ⟨fun i => (aPlusQ_int D j τ i).choose_spec.symm,
      fun c => by push_cast; rw [← (aMinusQ_int D j τ c).choose_spec]⟩⟩

def lamTr (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) : ℝ :=
  (LinearMap.trace ℂ (D.what₂.Mj j)
    (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j π).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re /
    (Module.finrank ℂ (D.what₂.isot j π) : ℝ)

def LamDef (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ → D.what₂.lamP μ j π = lamTr D μ j π

theorem lamTr_of_scalar (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) (c : ℝ) (h0 : D.what₂.isot j π ≠ ⊥)
    (hc : ∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = (c : ℂ) • x) : lamTr D μ j π = c := by
  set W := D.what₂.isot j π with hW
  have hP : LinearMap.IsProj W (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) :=
    ⟨fun x => W.starProjection_apply_mem x, fun x hx => Submodule.starProjection_eq_self_iff.2 hx⟩
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) =
      (c : ℂ) • (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) := by
    ext y
    exact hc _ (W.starProjection_apply_mem y)
  have hf : (Module.finrank ℂ W : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℂ W := Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)
    exact_mod_cast this.ne'
  show (LinearMap.trace ℂ (D.what₂.Mj j) (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ
    (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re / (Module.finrank ℂ W : ℝ) = c
  rw [hT, map_smul, hP.trace, smul_eq_mul]
  have : ((c : ℂ) * ((Module.finrank ℂ W : ℕ) : ℂ)).re = c * (Module.finrank ℂ W : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this, mul_div_assoc, div_self hf, mul_one]

def lamProd (D : D7) {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  ∏ σ, ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ)

end DV

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def iiStar : EE →ₗ[ℂ] EE := S.iotaQ D.what₂.mu0 ∘ₗ LinearMap.adjoint (S.iotaQ D.what₂.mu0)

def kapRatio {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ := (LinearMap.det S.iiStar).re / DV.lamProd D ty

def kapOf {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  if 0 < S.kapRatio ty then S.kapRatio ty ^ ((n : ℝ)⁻¹) else 1

theorem kapOf_pos {n : ℕ} (ty : Fin n → D.what₂.FT) : 0 < S.kapOf ty := by
  unfold kapOf
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

end RowSide

def kapSharp (D : D7) : ℝ := (RowSide.sharp D).kapOf D.what₂.ft

def BaseLevelRowSide.kap0 {D : D7} (X : BaseLevelRowSide D) : ℝ := X.s.kapOf D.what₂.ft0

def DV.KapRBase {D : D7} (X : DivX D) : Prop := X.kapR D.what₂.embLL = kapSharp D

end Formalism.BasicNotions

end
