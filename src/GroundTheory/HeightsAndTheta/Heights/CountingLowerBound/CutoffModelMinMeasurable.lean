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

def ReductionSmallLast.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0

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

def ReductionSmallFirst.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallFirst.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0

structure InteriorDichotomy.Hyp (C0 C1 C2 h hmu g fj La : ℝ) : Prop where
  one_le_g : 1 ≤ g
  one_le_fj : 1 ≤ fj
  g_le_exp : g ≤ Real.exp La
  one_le_La : 1 ≤ La
  lower : -(fj * (C0 * Real.log (2 + g + max h 0) + C1 * La)) ≤ hmu
  upper : h ≤ 2 * hmu + C2 * g * La

def InteriorDichotomy.Statement : Prop :=
  ∀ C0 C1 C2 : ℝ, 0 ≤ C0 → 0 ≤ C1 → 0 ≤ C2 → ∃ C : ℝ,
    ∀ h hmu g fj La : ℝ, InteriorDichotomy.Hyp C0 C1 C2 h hmu g fj La → -(C * fj * La) ≤ hmu

structure AvoidMatrixLemma.Hyp (a c N x : ℝ) : Prop where
  a_pos : 0 < a
  c_pos : 0 < c
  N_pos : 0 < N
  x_nonneg : 0 ≤ x

def AvoidMatrixLemma.Statement : Prop :=
  ∀ a c N x : ℝ, AvoidMatrixLemma.Hyp a c N x →
    -(a * Real.log (c + 2 * a * N)) ≤ x / 2 - a * Real.log (c + N * x)

def shortestLength {V : Type*} [NormedAddCommGroup V] (L : Submodule ℤ V) : ℝ :=
  sInf ((fun v : V => ‖v‖) '' {v : V | v ∈ L ∧ v ≠ 0})

def MinkowskiCovolumeBound.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L],
    1 ≤ Module.finrank ℝ V →
      (shortestLength L / Real.sqrt (Module.finrank ℝ V)) ^ Module.finrank ℝ V ≤
        ZLattice.covolume L

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

def CuspWeightBound.Statement : Prop :=
  ∀ (f j' ρ : ℕ) (rd lam NI covol : ℝ), CuspWeightBound.Hyp f j' ρ rd lam NI covol →
    -Real.log NI ≤
      (f : ℝ) * j' * (2 * max 0 (Real.log (1 / lam)) + Real.log (2 * f * j' * rd))

structure ShortVectorsOrthogonal.Hyp {L : Type*} [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ)
    (a : L →+ L) (vr : ℝ) : Prop where
  len_nonneg : ∀ v, 0 ≤ len v
  form_le : ∀ v w, |(E v w : ℝ)| ≤ len v * len w
  map_le : ∀ v, len (a v) ≤ vr * len v
  vr_pos : 0 < vr

def ShortVectorsOrthogonal.Statement : Prop :=
  ∀ (L : Type u) [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ) (a : L →+ L) (vr : ℝ),
    ShortVectorsOrthogonal.Hyp len E a vr →
      ∀ v w : L, len v < vr ^ (-(1 / 2 : ℝ)) → len w < vr ^ (-(1 / 2 : ℝ)) → E (a v) w = 0

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

def PackingCount.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (L : Set V) (lam : ℝ)
    (W : Submodule ℝ V) (a : ℕ) (r : ℝ), PackingCount.Hyp L lam W a r →
      {v : V | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.Finite ∧
        (({v : V | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ a

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

def MeanCountBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r : ℝ, 0 < r → meanCount μ cnt r ≤ 2 * 36 ^ a

def TailBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r x : ℝ, 0 < r → 0 ≤ x →
        μ.real {z | lam z < Real.exp (-x) * r} ≤ min 1 (2 * 36 ^ a * Real.exp (-(ka * x)))

def MeanLogPlus.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r : ℝ, 0 < r →
        Integrable (fun z => max 0 (Real.log (r / lam z))) μ ∧
          ∫ z, max 0 (Real.log (r / lam z)) ∂μ ≤ 3

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

def MeanCountBoundUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r : ℝ, 0 < r → r ≤ R → meanCount μ cnt r ≤ 2 * 36 ^ a

def TailBoundUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r x : ℝ, 0 < r → r ≤ R → 0 ≤ x →
        μ.real {z | lam z < Real.exp (-x) * r} ≤ min 1 (2 * 36 ^ a * Real.exp (-(ka * x)))

def MeanLogPlusUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r : ℝ, 0 < r → r ≤ R →
        Integrable (fun z => max 0 (Real.log (r / lam z))) μ ∧
          ∫ z, max 0 (Real.log (r / lam z)) ∂μ ≤ 3

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

def MeanCuspWeight.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (U lam : X → ℝ)
    (f j' : ℕ) (rd vr : ℝ), MeanCuspWeight.Hyp μ U lam f j' rd vr →
      Integrable U μ ∧
        ∫ z, U z ∂μ ≤ (f : ℝ) * j' * (6 + Real.log vr + Real.log (2 * f * j' * rd))

structure TelescopeMetric.Hyp (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ) : Prop where
  telescope : A' - A = (1 / 2) * ∑ i ∈ Finset.range (n + 1), I i
  antitone : ∀ i, I (i + 1) ≤ I i

def TelescopeMetric.Statement : Prop :=
  ∀ (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ), TelescopeMetric.Hyp n A A' I →
    A' - ((n + 1 : ℝ) / 2) * I 0 ≤ A

structure LimitInEpsilon.Hyp (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ) : Prop where
  P_cont : ContinuousWithinAt P (Set.Ioi 0) 0
  Q_cont : ContinuousWithinAt Q (Set.Ioi 0) 0
  W_tendsto : Tendsto W (𝓝[>] 0) (𝓝 W0)
  ineq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((n : ℝ) + 1) * ((e' - ε * C1) * Q ε - (1 / 2) * W ε) ≤ P ε

def LimitInEpsilon.Statement : Prop :=
  ∀ (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ), LimitInEpsilon.Hyp n P Q W W0 e' C1 →
    ((n : ℝ) + 1) * (e' * Q 0 - W0 / 2) ≤ P 0

private lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  have := Real.exp_one_lt_d9
  linarith

private lemma log_three_le_two : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
  have := Real.add_one_le_exp (2 : ℝ)
  linarith

def cutoffModelMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance : IsProbabilityMeasure cutoffModelMeasure :=
  ⟨by simp [cutoffModelMeasure]⟩

def cutoffModelMin (x : ℝ) : ℝ := if 0 < x then x ^ ((3 : ℝ)⁻¹) else 1

def cutoffModelCount (t x : ℝ) : ℝ :=
  if cutoffModelMin x < t then (if t ≤ 1 then 1 else t ^ 3) else 0

lemma cutoffModelMin_measurable : Measurable cutoffModelMin :=
  Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

lemma cutoffModelMin_pos (x : ℝ) : 0 < cutoffModelMin x := by
  unfold cutoffModelMin
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

lemma cutoffModelMin_lt_iff {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cutoffModelMin x < t ↔ x < t ^ 3 := by
  rw [cutoffModelMin, if_pos hx]
  have h0 : 0 ≤ x ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg hx.le _
  rw [← pow_lt_pow_iff_left₀ h0 ht.le (by norm_num : (3 : ℕ) ≠ 0)]
  have h3 : (x ^ ((3 : ℝ)⁻¹)) ^ 3 = x := by
    have := Real.rpow_inv_natCast_pow hx.le (n := 3) (by norm_num)
    simpa using this
  rw [h3]

lemma cutoffModelCount_eq (t : ℝ) :
    cutoffModelCount t = Set.indicator {x | cutoffModelMin x < t} (fun _ => if t ≤ 1 then 1 else t ^ 3) := by
  funext x
  simp only [cutoffModelCount, Set.indicator_apply, Set.mem_ofPred_eq]

lemma cutoffModel_set_meas (t : ℝ) : MeasurableSet {x | cutoffModelMin x < t} :=
  measurableSet_lt cutoffModelMin_measurable measurable_const

lemma cutoffModel_meanCount {t : ℝ} (ht : 0 < t) :
    meanCount cutoffModelMeasure cutoffModelCount t = t ^ 3 := by
  rw [meanCount, cutoffModelCount_eq, integral_indicator_const _ (cutoffModel_set_meas t),
    smul_eq_mul, measureReal_def, cutoffModelMeasure,
    Measure.restrict_apply (cutoffModel_set_meas t)]
  by_cases h1 : t ≤ 1
  · have hset : {x | cutoffModelMin x < t} ∩ Set.Ioc 0 1 = Set.Ioo 0 (t ^ 3) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h, hx0, -⟩
        exact ⟨hx0, (cutoffModelMin_lt_iff hx0 ht).1 h⟩
      · rintro ⟨hx0, hx⟩
        exact ⟨(cutoffModelMin_lt_iff hx0 ht).2 hx, hx0,
          hx.le.trans (pow_le_one₀ ht.le h1)⟩
    rw [hset, Real.volume_Ioo, if_pos h1, sub_zero, ENNReal.toReal_ofReal (by positivity), mul_one]
  · have h1' : 1 < t := lt_of_not_ge h1
    have hset : {x | cutoffModelMin x < t} ∩ Set.Ioc 0 1 = Set.Ioc 0 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨hx0, hx1⟩
        exact ⟨(cutoffModelMin_lt_iff hx0 ht).2 (hx1.trans_lt (one_lt_pow₀ h1' (by norm_num))),
          hx0, hx1⟩
    rw [hset, Real.volume_Ioc, if_neg h1]
    norm_num

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBound
