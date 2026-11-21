import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre

noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspQuot

section Test

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set V} {α : V → ℂ}

def IsTest (U : Set V) (α : V → ℂ) : Prop := ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U

theorem IsTest.continuous_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Continuous fun x => α x * G x :=
  continuous_of_tsupport fun x hx => h.1.continuous.continuousAt.mul
    (hG.continuousAt (hU.mem_nhds (h.2.2 (tsupport_mul_subset_left hx))))

theorem IsTest.add {β : V → ℂ} (h : IsTest U α) (h' : IsTest U β) : IsTest U (α + β) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, (tsupport_add α β).trans (Set.union_subset h.2.2 h'.2.2)⟩

theorem IsTest.mul (h : IsTest U α) {β : V → ℂ} (hβ : ContDiff ℝ ∞ β) : IsTest U fun x => α x * β x :=
  ⟨h.1.mul hβ, h.2.1.mul_right, tsupport_mul_subset_left.trans h.2.2⟩

theorem IsTest.fderiv (h : IsTest U α) (v : V) : IsTest U fun x => fderiv ℝ α x v :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem isTest_zero : IsTest U (0 : V → ℂ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

theorem IsTest.integrable_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Integrable (fun x => α x * G x) ν :=
  (h.continuous_mul hU hG).integrable_of_hasCompactSupport h.2.1.mul_right

end Test

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (φ : GA E a → ℂ) (x : GA E a) : ℂ :=
  ∫ y, α y * chart φ x y ∂ν

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

variable {μ} [μ.IsMulRightInvariant] {S : Submodule ℂ (L2 (latticeGL E a) μ)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in
theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin a) (Cinf E) → Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact Units.isOpenEmbedding_val
end

theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Continuous fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 := by
  refine continuous_of_tsupport fun p hp => (hα.1.continuous.comp continuous_snd).continuousAt.mul ?_
  have h1 : p.2 ∈ tsupport α := by
    refine (closure_minimal (fun q hq => ?_) ((isClosed_tsupport α).preimage continuous_snd) :
      _ ⊆ Prod.snd ⁻¹' tsupport α) hp
    exact subset_tsupport _ (left_ne_zero_of_mul hq)
  obtain ⟨x, y⟩ := p
  obtain ⟨u, hu⟩ := hα.2.2 h1
  obtain rfl : y = toL u.val := hu.symm
  have he : IsOpenEmbedding (Prod.map id fun u : GL (Fin a) (Cinf E) => toL u.val : GA E a × _ → GA E a × Lie E a) :=
    IsOpenEmbedding.id.prodMap isOpenEmbedding_val
  refine (he.continuousAt_iff (x := (x, u))).1 (Continuous.continuousAt ?_)
  exact (hφ.comp (continuous_fst.mul (continuous_infGL.comp continuous_snd))).congr fun q => (chart_val φ q.1 q.2).symm

theorem norm_chart_le {φ : GA E a → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (x : GA E a) (y : Lie E a) : ‖chart φ x y‖ ≤ C := by
  unfold chart
  split_ifs
  · exact hC _
  · exact norm_zero.trans_le ((norm_nonneg _).trans (hC 1))

theorem continuous_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    Continuous (smoothing ν α φ) :=
  continuous_of_dominated (bound := fun y => ‖α y‖ * C)
    (fun x => ((continuous_integrand hα hφ).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun x => .of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC x y) (norm_nonneg _)))
    ((hα.1.continuous.integrable_of_hasCompactSupport hα.2.1).norm.mul_const C)
    (.of_forall fun y => (continuous_integrand hα hφ).comp (Continuous.prodMk_left y))

variable [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)]

omit [μ.IsMulRightInvariant] in

theorem memL2_of_bound {φ : GA E a → ℂ} (hφ : Continuous φ) (hl : LeftInv (latticeGL E a) φ) {C : ℝ}
    (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ :=
  ⟨hl, MemLp.of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (by
    rw [hl.lift_descend]; exact hφ.aestronglyMeasurable)) C (.of_forall fun q => hC _)⟩

end GlobalTheory.CuspQuot

end
