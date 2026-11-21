import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaIsoLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace Uniformity

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

def annSeminorm : RingSeminorm (T.Econ ρ0) where
  toFun b := max (T.gaussSeminorm ρ0 σ0 b) (T.gaussSeminorm ρ0 (topRad ρ0) b)
  map_zero' := by simp
  add_le' a b := max_le
    (((T.gaussSeminorm ρ0 σ0).add_le' a b).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (((T.gaussSeminorm ρ0 (topRad ρ0)).add_le' a b).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _)))
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have h0 : ∀ (f : RingSeminorm (T.Econ ρ0)) (x : T.Econ ρ0), 0 ≤ f x := fun f x => apply_nonneg f x
    refine max_le (((T.gaussSeminorm ρ0 σ0).mul_le' a b).trans ?_)
      (((T.gaussSeminorm ρ0 (topRad ρ0)).mul_le' a b).trans ?_)
    · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))

theorem annSeminorm_apply (b : T.Econ ρ0) :
    T.annSeminorm ρ0 σ0 b = max (gaussNorm (T.coeffB b) σ0) (gaussNorm (T.coeffB b) ρ0) := rfl

abbrev AnnRad := Set.Icc ((σ0 : ℝ)) (ρ0 : ℝ)

variable {ρ0 σ0} in

def annIoc (r : AnnRad ρ0 σ0) : Set.Ioc (0 : ℝ) ρ0 := ⟨r, σ0.2.1.trans_le r.2.1, r.2.2⟩

@[simp] theorem coe_annIoc {r : AnnRad ρ0 σ0} : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = r := rfl

def annIn : AnnRad ρ0 σ0 := ⟨σ0, le_rfl, σ0.2.2⟩

def annOut : AnnRad ρ0 σ0 := ⟨ρ0, σ0.2.2, le_rfl⟩

@[simp] theorem coe_annIn : ((annIn ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = σ0 := rfl

@[simp] theorem coe_annOut : ((annOut ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = ρ0 := rfl

variable {ρ0 σ0} in

theorem gaussNorm_le_annSeminorm (b : T.Econ ρ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB b) r ≤ T.annSeminorm ρ0 σ0 b :=
  gaussNorm_le_max σ0.2.1 r.2.1 r.2.2 (T.convergesAt_rad ρ0 b σ0) (T.convergesAt_rad ρ0 b (topRad ρ0))

@[nolint unusedArguments]
def AnnCore (_σ0 : Set.Ioc (0 : ℝ) ρ0) : Type _ := T.Econ ρ0

instance : CommRing (T.AnnCore ρ0 σ0) := inferInstanceAs (CommRing (T.Econ ρ0))

instance : PseudoMetricSpace (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toSeminormedRing.toPseudoMetricSpace

instance : IsUniformAddGroup (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup

instance : IsTopologicalRing (T.AnnCore ρ0 σ0) := by
  have : ContinuousMul (T.AnnCore ρ0 σ0) :=
    @NonUnitalSeminormedRing.toContinuousMul _
      (T.annSeminorm ρ0 σ0).toSeminormedRing.toNonUnitalSeminormedRing
  exact {}

abbrev Ann := UniformSpace.Completion (T.AnnCore ρ0 σ0)

def coreOf : T.Econ ρ0 →+* T.AnnCore ρ0 σ0 := RingHom.id (T.Econ ρ0)

def coreVal (b : T.AnnCore ρ0 σ0) : T.B := ((show T.Econ ρ0 from b) : T.B)

variable {ρ0 σ0}

@[simp] theorem coreVal_coreOf (b : T.Econ ρ0) : T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b) = b := rfl

theorem coreVal_sub (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a - b) = T.coreVal ρ0 σ0 a - T.coreVal ρ0 σ0 b := rfl

theorem coreVal_add (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a + b) = T.coreVal ρ0 σ0 a + T.coreVal ρ0 σ0 b := rfl

theorem coreVal_mul (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a * b) = T.coreVal ρ0 σ0 a * T.coreVal ρ0 σ0 b := rfl

theorem coreVal_neg (a : T.AnnCore ρ0 σ0) : T.coreVal ρ0 σ0 (-a) = -T.coreVal ρ0 σ0 a := rfl

theorem coreVal_one : T.coreVal ρ0 σ0 1 = 1 := rfl

theorem coreVal_zero : T.coreVal ρ0 σ0 0 = 0 := rfl

theorem convergesAt_coreVal (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    ConvergesAt (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  T.convergesAt_rad ρ0 (show T.Econ ρ0 from b) (annIoc r)

theorem dist_annCore (a b : T.AnnCore ρ0 σ0) :
    dist a b = max (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (a - b))) σ0)
      (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (a - b))) ρ0) := by
  change T.annSeminorm ρ0 σ0 (-(show T.Econ ρ0 from a) + (show T.Econ ρ0 from b)) = _
  rw [neg_add_eq_sub, ← neg_sub, map_neg_eq_map, annSeminorm_apply]
  rfl

def coeAnn : T.Econ ρ0 →+* T.Ann ρ0 σ0 := (Completion.coeRingHom).comp (T.coreOf ρ0 σ0)

theorem coeAnn_apply (b : T.Econ ρ0) :
    T.coeAnn b = ((T.coreOf ρ0 σ0 b : T.AnnCore ρ0 σ0) : T.Ann ρ0 σ0) := rfl

theorem gaussNorm_coreVal_le (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r ≤
      max (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) σ0) (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) ρ0) :=
  T.gaussNorm_le_annSeminorm (show T.Econ ρ0 from b) r

theorem gaussNorm_coreVal_nonneg (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    0 ≤ gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  gaussNorm_nonneg (σ0.2.1.trans_le r.2.1)

theorem abs_gaussNorm_sub_le (a b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    |gaussNorm (T.coeffB (T.coreVal ρ0 σ0 a)) r - gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r| ≤
      dist a b := by
  have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
  have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
  have key : ∀ x y : T.AnnCore ρ0 σ0, gaussNorm (T.coeffB (T.coreVal ρ0 σ0 x)) r ≤
      gaussNorm (T.coeffB (T.coreVal ρ0 σ0 y)) r + dist x y := by
    intro x y
    have e : T.coreVal ρ0 σ0 x = T.coreVal ρ0 σ0 y + T.coreVal ρ0 σ0 (x - y) := by
      rw [coreVal_sub]; ring
    have h1 := (T.convergesAt_coeffB_add hr0 hr1 (T.convergesAt_coreVal y r)
      (T.convergesAt_coreVal (x - y) r)).2
    rw [← e] at h1
    refine h1.trans ((max_le_add_of_nonneg (T.gaussNorm_coreVal_nonneg _ r)
      (T.gaussNorm_coreVal_nonneg _ r)).trans (add_le_add le_rfl ?_))
    rw [dist_annCore]
    exact T.gaussNorm_coreVal_le (x - y) r
  rw [abs_sub_le_iff]
  constructor
  · linarith [key a b]
  · linarith [key b a, dist_comm a b]

theorem uniformContinuous_gaussNorm_ann (r : AnnRad ρ0 σ0) :
    UniformContinuous (fun b : T.AnnCore ρ0 σ0 => gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r) :=
  LipschitzWith.uniformContinuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    exact T.abs_gaussNorm_sub_le a b r)

variable (ρ0 σ0) in

def annNorm (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) : ℝ :=
  Completion.extension (fun b : T.AnnCore ρ0 σ0 => gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r) x

theorem annNorm_coe (r : AnnRad ρ0 σ0) (b : T.AnnCore ρ0 σ0) :
    T.annNorm ρ0 σ0 r (b : T.Ann ρ0 σ0) = gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  Completion.extension_coe (T.uniformContinuous_gaussNorm_ann r) b

theorem annNorm_coeAnn (r : AnnRad ρ0 σ0) (b : T.Econ ρ0) :
    T.annNorm ρ0 σ0 r (T.coeAnn b) = gaussNorm (T.coeffB b) r :=
  T.annNorm_coe r _

theorem continuous_annNorm (r : AnnRad ρ0 σ0) : Continuous (T.annNorm ρ0 σ0 r) :=
  Completion.continuous_extension

theorem annNorm_nonneg (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) : 0 ≤ T.annNorm ρ0 σ0 r x :=
  Completion.induction_on x (isClosed_le continuous_const (T.continuous_annNorm r))
    fun b => by rw [annNorm_coe]; exact T.gaussNorm_coreVal_nonneg b r

theorem annNorm_mul (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x * y) = T.annNorm ρ0 σ0 r x * T.annNorm ρ0 σ0 r y :=
  Completion.induction_on₂ x y
    (isClosed_eq ((T.continuous_annNorm r).comp continuous_mul)
      (((T.continuous_annNorm r).comp continuous_fst).mul ((T.continuous_annNorm r).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_mul, annNorm_coe, annNorm_coe, annNorm_coe, coreVal_mul]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_mul hr0 hr1 (T.convergesAt_coreVal a r) (T.convergesAt_coreVal b r)).2

theorem annNorm_add_le (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x + y) ≤ max (T.annNorm ρ0 σ0 r x) (T.annNorm ρ0 σ0 r y) :=
  Completion.induction_on₂ x y
    (isClosed_le ((T.continuous_annNorm r).comp continuous_add)
      (((T.continuous_annNorm r).comp continuous_fst).max ((T.continuous_annNorm r).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_add, annNorm_coe, annNorm_coe, annNorm_coe, coreVal_add]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_add hr0 hr1 (T.convergesAt_coreVal a r) (T.convergesAt_coreVal b r)).2

theorem annNorm_neg (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (-x) = T.annNorm ρ0 σ0 r x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm r).comp continuous_neg) (T.continuous_annNorm r))
    fun a => by
      rw [← Completion.coe_neg, annNorm_coe, annNorm_coe, coreVal_neg]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_neg hr0 hr1 (T.convergesAt_coreVal a r)).2

theorem annNorm_sub_comm (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x - y) = T.annNorm ρ0 σ0 r (y - x) := by
  rw [← neg_sub, annNorm_neg]

theorem annNorm_zero (r : AnnRad ρ0 σ0) : T.annNorm ρ0 σ0 r 0 = 0 := by
  rw [← Completion.coe_zero, annNorm_coe, coreVal_zero, ← map_zero (algebraMap Γ T.B),
    coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
  simp [gaussNorm]

theorem dist_ann (x y : T.Ann ρ0 σ0) :
    dist x y = max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - y)) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - y)) :=
  Completion.induction_on₂ x y
    (isClosed_eq continuous_dist
      (((T.continuous_annNorm _).comp (continuous_fst.sub continuous_snd)).max
        ((T.continuous_annNorm _).comp (continuous_fst.sub continuous_snd))))
    fun a b => by
      rw [Completion.dist_eq, ← Completion.coe_sub, annNorm_coe, annNorm_coe, dist_annCore]
      rfl

theorem eq_of_annNorm_sub {x y : T.Ann ρ0 σ0} (hlo : T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - y) = 0)
    (hhi : T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - y) = 0) : x = y := by
  rw [← dist_eq_zero, dist_ann, hlo, hhi, max_self]

theorem exists_limit_ann {z : ℕ → T.Ann ρ0 σ0}
    (h : ∀ ε > 0, ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ K ≥ J₀, T.annNorm ρ0 σ0 (annIn ρ0 σ0) (z J - z K) ≤ ε ∧
      T.annNorm ρ0 σ0 (annOut ρ0 σ0) (z J - z K) ≤ ε) :
    ∃ x : T.Ann ρ0 σ0, ∀ r : AnnRad ρ0 σ0, Tendsto (fun J => T.annNorm ρ0 σ0 r (z J - x)) atTop (𝓝 0) := by
  have hc : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := h (ε / 2) (half_pos hε)
    refine ⟨J₀, fun J hJ => ?_⟩
    rw [dist_ann]
    obtain ⟨h1, h2⟩ := hJ₀ J hJ J₀ le_rfl
    exact lt_of_le_of_lt (max_le h1 h2) (half_lt_self hε)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun r => ?_⟩
  have h0 : Tendsto (fun J => T.annNorm ρ0 σ0 r (z J - x)) atTop (𝓝 (T.annNorm ρ0 σ0 r (x - x))) :=
    ((T.continuous_annNorm r).tendsto _).comp (hx.sub tendsto_const_nhds)
  rwa [sub_self, annNorm_zero] at h0

section Res

variable {ρ1 : Set.Ioo (0 : ℝ) 1} (σ1 : Set.Ioc (0 : ℝ) ρ1) (h : (ρ1 : ℝ) ≤ ρ0)

variable {σ1} in

def annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) : AnnRad ρ0 σ0 :=
  ⟨r, hσ.trans r.2.1, r.2.2.trans h⟩

variable {σ1} in
@[simp] theorem coe_annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) :
    ((annRadOf h hσ r : AnnRad ρ0 σ0) : ℝ) = r := rfl

def coreIncl : T.AnnCore ρ0 σ0 →+* T.AnnCore ρ1 σ1 := T.incl h

theorem coreVal_coreIncl (b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ1 σ1 (T.coreIncl σ1 h b) = T.coreVal ρ0 σ0 b := rfl

variable {σ1} (hσ : (σ0 : ℝ) ≤ σ1)

end Res

namespace TeichFrob

variable {T} (F : T.TeichFrob)

def annPowRad (r : AnnRad ρ0 σ0) : AnnRad (F.powRadius ρ0) (F.powRad σ0) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_le_pow_left₀ σ0.2.1.le r.2.1 _, pow_le_pow_left₀ (σ0.2.1.trans_le r.2.1).le r.2.2 _⟩

@[simp] theorem coe_annPowRad (r : AnnRad ρ0 σ0) :
    ((F.annPowRad r : AnnRad (F.powRadius ρ0) (F.powRad σ0)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

def coreFrob : T.AnnCore ρ0 σ0 →+* T.AnnCore (F.powRadius ρ0) (F.powRad σ0) := F.econFrob ρ0

theorem coreVal_coreFrob (b : T.AnnCore ρ0 σ0) :
    T.coreVal _ _ (F.coreFrob b) = F.toB (T.coreVal ρ0 σ0 b) := rfl

end TeichFrob

namespace TeichIso

variable {T} (G : T.TeichIso)

def coreMap : T.AnnCore ρ0 σ0 →+* T.AnnCore ρ0 σ0 := G.econMap ρ0

theorem coreVal_coreMap (b : T.AnnCore ρ0 σ0) : T.coreVal ρ0 σ0 (G.coreMap b) = G.toB (T.coreVal ρ0 σ0 b) :=
  rfl

end TeichIso

end TeichLift

end GroundTheory.PAdicHodge
