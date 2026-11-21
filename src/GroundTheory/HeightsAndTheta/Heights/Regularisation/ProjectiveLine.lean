import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights (CP)
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace ProjectiveLine

def sChart (i : Fin 2) : OpenPartialHomeomorph (CP 1) (Fin 1 → ℂ) where
  toFun x := (2 : ℂ)⁻¹ • CP.chartCoord i x
  invFun y := CP.chartInv i ((2 : ℂ) • y)
  source := CP.chartDomain i ∩ CP.chartCoord i ⁻¹' ball 0 2
  target := ball 0 1
  map_source' x hx := by
    have h := hx.2
    simp only [mem_preimage, mem_ball_zero_iff] at h ⊢
    rw [norm_smul]
    norm_num
    linarith
  map_target' y hy := by
    refine ⟨CP.chartInv_mem i _, ?_⟩
    simp only [mem_preimage, CP.chartCoord_chartInv, mem_ball_zero_iff] at hy ⊢
    rw [norm_smul]
    norm_num
    linarith
  left_inv' x hx := by
    simp only [smul_smul]
    norm_num
    exact CP.chartInv_chartCoord i hx.1
  right_inv' y _ := by
    simp only [CP.chartCoord_chartInv, smul_smul]
    norm_num
  open_source := (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i)
    isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := ((CP.continuousOn_chartCoord i).mono inter_subset_left).const_smul ((2 : ℂ)⁻¹)
  continuousOn_invFun := ((CP.continuous_chartInv i).comp (continuous_const_smul _)).continuousOn

theorem sChart_apply (i : Fin 2) (x : CP 1) : sChart i x = (2 : ℂ)⁻¹ • CP.chartCoord i x := rfl

theorem sChart_symm_apply (i : Fin 2) (y : Fin 1 → ℂ) :
    (sChart i).symm y = CP.chartInv i ((2 : ℂ) • y) := rfl

theorem sChart_source (i : Fin 2) :
    (sChart i).source = CP.chartDomain i ∩ CP.chartCoord i ⁻¹' ball 0 2 := rfl

theorem sChart_target (i : Fin 2) : (sChart i).target = ball 0 1 := rfl

def ltSet (a b : Fin 2) : Set (CP 1) :=
  {x | Projectivization.lift (fun v : {v : Fin 2 → ℂ // v ≠ 0} => ‖v.1 a‖ < ‖v.1 b‖) (by
    rintro ⟨u, hu⟩ ⟨w, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hu
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact propext (mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ht))) x}

theorem mk_mem_ltSet (a b : Fin 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ ltSet a b ↔ ‖v a‖ < ‖v b‖ := Iff.rfl

theorem isOpen_ltSet (a b : Fin 2) : IsOpen (ltSet a b) := by
  rw [GroundTheory.Heights₂.Heights.ProjTopology.isOpen_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (ltSet a b) =
      {v : {v : Fin 2 → ℂ // v ≠ 0} | ‖v.1 a‖ < ‖v.1 b‖} := by
    ext ⟨v, hv⟩; exact Iff.rfl
  rw [this]
  exact isOpen_lt ((continuous_apply a).comp continuous_subtype_val).norm
    ((continuous_apply b).comp continuous_subtype_val).norm

theorem mem_ltSet_of_not_mem (a b : Fin 2) (hab : a ≠ b) (x : CP 1) (hx : x ∉ CP.chartDomain a) :
    x ∈ ltSet a b := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [CP.mk_mem_chartDomain, not_not] at hx
    rw [mk_mem_ltSet, hx, norm_zero, norm_pos_iff]
    intro hb
    apply hv
    funext m
    fin_cases a <;> fin_cases b <;> fin_cases m <;> simp_all

instance t2Space_complexProjLine : T2Space (CP 1) := by
  refine ⟨fun x y hxy => ?_⟩
  have key : ∀ i : Fin 2, x ∈ CP.chartDomain i → y ∈ CP.chartDomain i →
      ∃ u v : Set (CP 1), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
    intro i hx hy
    have hne : CP.chartCoord i x ≠ CP.chartCoord i y := fun h => hxy (by
      rw [← CP.chartInv_chartCoord i hx, h, CP.chartInv_chartCoord i hy])
    obtain ⟨u', v', hu', hv', hxu, hyv, huv⟩ := t2_separation hne
    refine ⟨CP.chartDomain i ∩ CP.chartCoord i ⁻¹' u', CP.chartDomain i ∩ CP.chartCoord i ⁻¹' v',
      (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i) hu',
      (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i) hv',
      ⟨hx, hxu⟩, ⟨hy, hyv⟩, ?_⟩
    exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 huv hz.2 hz'.2
  have hdisj : Disjoint (ltSet 0 1) (ltSet 1 0) :=
    Set.disjoint_left.2 fun z hz hz' => by
      induction z using Projectivization.ind with
      | h v hv =>
        rw [mk_mem_ltSet] at hz hz'
        exact lt_asymm hz hz'
  by_cases h0 : x ∈ CP.chartDomain 0 ∧ y ∈ CP.chartDomain 0
  · exact key 0 h0.1 h0.2
  by_cases h1 : x ∈ CP.chartDomain 1 ∧ y ∈ CP.chartDomain 1
  · exact key 1 h1.1 h1.2
  by_cases hx0 : x ∈ CP.chartDomain 0
  ·
    have hy0 : y ∉ CP.chartDomain 0 := fun hy => h0 ⟨hx0, hy⟩
    have hx1 : x ∉ CP.chartDomain 1 := by
      intro hx1
      obtain ⟨i, hi⟩ := CP.exists_mem_chartDomain y
      fin_cases i
      · exact hy0 hi
      · exact h1 ⟨hx1, hi⟩
    exact ⟨ltSet 1 0, ltSet 0 1, isOpen_ltSet 1 0, isOpen_ltSet 0 1,
      mem_ltSet_of_not_mem 1 0 (by decide) x hx1, mem_ltSet_of_not_mem 0 1 (by decide) y hy0,
      hdisj.symm⟩
  · have hy1 : y ∉ CP.chartDomain 1 := by
      intro hy1
      obtain ⟨i, hi⟩ := CP.exists_mem_chartDomain x
      fin_cases i
      · exact hx0 hi
      · exact h1 ⟨hi, hy1⟩
    exact ⟨ltSet 0 1, ltSet 1 0, isOpen_ltSet 0 1, isOpen_ltSet 1 0,
      mem_ltSet_of_not_mem 0 1 (by decide) x hx0, mem_ltSet_of_not_mem 1 0 (by decide) y hy1,
      hdisj⟩

end ProjectiveLine

end

end GroundTheory.Heights₂.Heights.Regular
