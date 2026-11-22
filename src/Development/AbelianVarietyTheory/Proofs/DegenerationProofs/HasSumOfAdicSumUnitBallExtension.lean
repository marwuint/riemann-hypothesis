import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AdicNormSum

open Filter Topology in
private lemma exists_norm_le_mul_of_mem_ideal_smul_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] {_ : Module R C} (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1)
    (hsmul : ∀ (r : R) (y : C), r • y = φ r * y) {N : Submodule R C} (hN : N.FG) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (J : Ideal R) (t : ℝ), 0 ≤ t → (∀ r ∈ J, ‖φ r‖ ≤ t) →
      ∀ y ∈ J • N, ‖y‖ ≤ t * M := by
  obtain ⟨G, rfl⟩ := hN
  have hbound : ∀ y ∈ Submodule.span R (G : Set C), ‖y‖ ≤ (G.sup fun g => ‖g‖₊ : NNReal) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [hsmul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb
  refine ⟨(G.sup fun g => ‖g‖₊ : NNReal), NNReal.coe_nonneg _, ?_⟩
  intro J t ht hJ y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    rw [hsmul, norm_mul]
    exact mul_le_mul (hJ r hr) (hbound z hz) (norm_nonneg _) ht
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

open Filter Topology in
private lemma exists_uniform_norm_bound_lt_one_of_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} (hfg : I.FG)
    (hI : ∀ r ∈ I, ‖φ r‖ < 1) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ r ∈ I, ‖φ r‖ ≤ c := by
  obtain ⟨G, rfl⟩ := hfg
  refine ⟨(G.sup fun g => ‖φ g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, ?_⟩
  · have h : G.sup (fun g => ‖φ g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hg' := hI g (Ideal.subset_span hg)
      exact_mod_cast hg'
    exact_mod_cast h
  · intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖φ g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

open Filter Topology in
private lemma hasSum_of_norm_sub_le_geometric {Ix E : Type} [NormedAddCommGroup E]
    {x : Ix → E} {s : E} {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ‖s - ∑ i ∈ T, x i‖ ≤ c ^ n * M) :
    HasSum x s := by
  show Tendsto (fun T : Finset Ix => ∑ i ∈ T, x i) atTop (𝓝 s)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun n : ℕ => c ^ n * M) atTop (𝓝 (0 * M)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const M
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.eventually_atTop.2 ⟨S, fun T hT => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (hS T hT).trans_lt hn

open Filter Topology in
private lemma norm_le_pow_of_mem_ideal_pow {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} {c : ℝ}
    (hc0 : 0 ≤ c) (hI : ∀ r ∈ I, ‖φ r‖ ≤ c) : ∀ n : ℕ, ∀ r ∈ I ^ n, ‖φ r‖ ≤ c ^ n := by
  intro n
  induction n with
  | zero => intro r _; simpa using hφ r
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hI b hb) (norm_nonneg _) (pow_nonneg hc0 n)
    · intro a b ha hb
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

open Filter Topology in

theorem _root_.GlobalTheory.Ex.AdicNormSum.main : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing R) C], _root_.GlobalTheory.Ex.CExt R I C → ∀ (Ix : Type) (x : Ix → C)
    (s : C), _root_.GlobalTheory.UT.SumF I C x s → HasSum x s := by
  intro R _ _ _ I C _ _ _ hC Ix x s hs
  obtain ⟨hle, hlt⟩ := hC
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  have hs' : _root_.GlobalTheory.UT.SumI I x s := hs
  unfold _root_.GlobalTheory.UT.SumI at hs'
  obtain ⟨N, hNfg, -, -, hconv⟩ := hs'
  let φ : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R (FractionRing R))
  have hφ : ∀ r, ‖φ r‖ ≤ 1 := hle
  obtain ⟨M, -, hM⟩ := exists_norm_le_mul_of_mem_ideal_smul_fg (N := N) φ hφ
    (fun r y => Algebra.smul_def (algebraMap R (FractionRing R) r) y) hNfg
  obtain ⟨c, hc0, hc1, hcI⟩ := exists_uniform_norm_bound_lt_one_of_fg φ hφ (IsNoetherian.noetherian I) hlt
  exact hasSum_of_norm_sub_le_geometric hc0 hc1 fun n => (hconv n).imp fun S hS T hT =>
    hM (I ^ n) (c ^ n) (pow_nonneg hc0 n) (norm_le_pow_of_mem_ideal_pow φ hφ hc0 hcI n) _ (hS T hT)

end GlobalTheory.Ex.AdicNormSum
