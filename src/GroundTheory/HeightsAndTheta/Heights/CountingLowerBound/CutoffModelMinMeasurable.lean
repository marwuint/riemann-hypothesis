import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBound

open MeasureTheory Filter Topology

noncomputable section

universe u

structure ReductionSmallLast.Hyp (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le_j : N / 2 ≤ j
  j_pos : 0 < j
  one_le_La : 1 ≤ La
  log_le_La : Real.log (N + 1) ≤ La
  formula : f * j' * b0 = hh / ((n + 1) * J) - sl + rest / ((n + 1) * vol * J)
  bound_c : |j * A0 + N * b0| ≤ K1 * N * La
  bound_sl : -(Ca * f * j' * La) ≤ sl
  bound_hh : hh / ((n + 1) * J) ≤ f * j' / 2 * Real.log (N + 1)
  bound_rest : |rest| ≤ Cc * f * j' * (n + 1) * vol * J

structure ReductionSmallFirst.Hyp (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le : N / 2 ≤ N - j
  sub_pos : 0 < N - j
  one_le_La : 1 ≤ La
  log_le_La : Real.log (N + 1) ≤ La
  formula : f * j' * (A0 + b0) = sl - hh / ((n + 1) * J) - rest / ((n + 1) * vol * J)
  bound_c : |j * A0 + N * b0| ≤ K1 * N * La
  bound_sl : -(Ca * f * j' * La) ≤ sl
  bound_hh : hh / ((n + 1) * J) ≤ f * j' / 2 * Real.log (N + 1)
  bound_rest : |rest| ≤ Cc * f * j' * (n + 1) * vol * J

structure InteriorDichotomy.Hyp (C0 C1 C2 h hmu g fj La : ℝ) : Prop where
  one_le_g : 1 ≤ g
  one_le_fj : 1 ≤ fj
  g_le_exp : g ≤ Real.exp La
  one_le_La : 1 ≤ La
  lower : -(fj * (C0 * Real.log (2 + g + max h 0) + C1 * La)) ≤ hmu
  upper : h ≤ 2 * hmu + C2 * g * La

structure AvoidMatrixLemma.Hyp (a c N x : ℝ) : Prop where
  a_pos : 0 < a
  c_pos : 0 < c
  N_pos : 0 < N
  x_nonneg : 0 ≤ x

structure CuspWeightBound.Hyp (f j' ρ : ℕ) (rd lam NI covol : ℝ) : Prop where
  one_le_f : 1 ≤ f
  one_le_j' : 1 ≤ j'
  one_le_ρ : 1 ≤ ρ
  ρ_le_j' : ρ ≤ j'
  one_le_rd : 1 ≤ rd
  lam_pos : 0 < lam
  NI_pos : 0 < NI
  covol_pos : 0 < covol
  covol_eq : covol = NI * rd ^ (f * ρ)
  minkowski : (lam / Real.sqrt (2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ covol

structure ShortVectorsOrthogonal.Hyp {L : Type*} [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ)
    (a : L →+ L) (vr : ℝ) : Prop where
  len_nonneg : ∀ v, 0 ≤ len v
  form_le : ∀ v w, |(E v w : ℝ)| ≤ len v * len w
  map_le : ∀ v, len (a v) ≤ vr * len v
  vr_pos : 0 < vr

structure PackingCount.Hyp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Set V) (lam : ℝ) (W : Submodule ℝ V) (a : ℕ) (r : ℝ) : Prop where
  zero_mem : (0 : V) ∈ L
  sub_mem : ∀ v ∈ L, ∀ w ∈ L, v - w ∈ L
  lam_pos : 0 < lam
  lam_le : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖
  finrank_eq : Module.finrank ℝ W = a
  one_le_a : 1 ≤ a
  short_mem : ∀ v ∈ L, ‖v‖ < r → v ∈ W
  lam_le_r : lam ≤ r

def meanCount {X : Type*} [MeasurableSpace X] (μ : Measure X) (cnt : ℝ → X → ℝ) (t : ℝ) : ℝ :=
  ∫ z, cnt t z ∂μ

structure MeanCountBound.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ) : Prop where
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  cnt_meas : ∀ t, Measurable (cnt t)
  cnt_nonneg : ∀ t z, 0 ≤ cnt t z
  one_le_a : 1 ≤ a
  three_a_le_ka : 3 * (a : ℝ) ≤ ka
  integrable : ∀ t, 0 < t → Integrable (cnt t) μ
  count_le : ∀ t, 0 < t → ∀ z, lam z < t → cnt t z ≤ (3 * t / lam z) ^ a
  count_zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → cnt t z = 0
  one_le_cnt : ∀ t z, lam z < t → 1 ≤ cnt t z
  scaling : ∀ θ t, 0 < θ → 0 < t → meanCount μ cnt (θ * t) = θ ^ ka * meanCount μ cnt t

structure MeanCountBoundUpTo.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ) : Prop where
  R_pos : 0 < R
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  cnt_meas : ∀ t, Measurable (cnt t)
  cnt_nonneg : ∀ t z, 0 ≤ cnt t z
  one_le_a : 1 ≤ a
  three_a_le_ka : 3 * (a : ℝ) ≤ ka
  integrable : ∀ t, 0 < t → Integrable (cnt t) μ
  count_le : ∀ t, 0 < t → t ≤ R → ∀ z, lam z < t → cnt t z ≤ (3 * t / lam z) ^ a
  count_zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → cnt t z = 0
  one_le_cnt : ∀ t, t ≤ R → ∀ z, lam z < t → 1 ≤ cnt t z
  scaling : ∀ θ t, 0 < θ → 0 < t → meanCount μ cnt (θ * t) = θ ^ ka * meanCount μ cnt t

structure MeanCuspWeight.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (U lam : X → ℝ)
    (f j' : ℕ) (rd vr : ℝ) : Prop where
  U_meas : Measurable U
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  U_nonneg : ∀ z, 0 ≤ U z
  one_le_f : 1 ≤ f
  one_le_j' : 1 ≤ j'
  one_le_rd : 1 ≤ rd
  one_le_vr : 1 ≤ vr
  U_le : ∀ z, U z ≤ (f : ℝ) * j' * (2 * max 0 (Real.log (1 / lam z)) + Real.log (2 * f * j' * rd))
  integrable : Integrable (fun z => max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam z))) μ
  mean_le : ∫ z, max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ ≤ 3

structure TelescopeMetric.Hyp (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ) : Prop where
  telescope : A' - A = (1 / 2) * ∑ i ∈ Finset.range (n + 1), I i
  antitone : ∀ i, I (i + 1) ≤ I i

structure LimitInEpsilon.Hyp (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ) : Prop where
  P_cont : ContinuousWithinAt P (Set.Ioi 0) 0
  Q_cont : ContinuousWithinAt Q (Set.Ioi 0) 0
  W_tendsto : Tendsto W (𝓝[>] 0) (𝓝 W0)
  ineq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((n : ℝ) + 1) * ((e' - ε * C1) * Q ε - (1 / 2) * W ε) ≤ P ε

def cutoffModelMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance : IsProbabilityMeasure cutoffModelMeasure :=
  ⟨by simp [cutoffModelMeasure]⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBound
