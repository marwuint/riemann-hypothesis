import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal

namespace GlobalTheory.RestrMeas

section Pi

theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod_eq_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod fun i => hf _

end Pi

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v}
  {K : ∀ v, Set (Yf v)}

theorem finprod_eq_prod_of_mem {M : Type} [CommMonoid M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) {x : X} (hx : ∀ v ∉ S, pf v x ∈ K v) :
    ∏ᶠ v, ff v (pf v x) = ∏ v ∈ S, ff v (pf v x) :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h' => hv (h1 v h' _ (hx v h'))

theorem finprod_eq_zero_of_notMem {M : Type} [CommMonoidWithZero M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ff v = (K v).indicator 1) {x : X} (hx : ∀ᶠ v in cofinite, pf v x ∈ K v)
    (hx' : ¬ ∀ v ∉ S, pf v x ∈ K v) : ∏ᶠ v, ff v (pf v x) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_of_eventually hx
  push Not at hx'
  obtain ⟨u, hu, hu'⟩ := hx'
  rw [finprod_eq_prod_of_mem (K := K) (S := S ∪ T)
    (fun v hv y hy => by rw [h1 v fun h' => hv (Finset.mem_union_left _ h'), indicator_of_mem hy, Pi.one_apply])
    fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')]
  exact Finset.prod_eq_zero (Finset.mem_union_right _ (by_contra fun h' => hu' (hT u h')))
    (by rw [h1 u hu, indicator_of_notMem hu'])

variable [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] [Countable V]

theorem measurableSet_level (hf : ∀ v, Measurable (pf v)) (hK : ∀ v, MeasurableSet (K v)) (S : Finset V) :
    MeasurableSet {x | ∀ v ∉ S, pf v x ∈ K v} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hf v (hK v)

variable [Fintype W] {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
  [∀ w, SigmaFinite (μa w)] [∀ v, SigmaFinite (μf v)]

omit [Countable V] in

theorem IsCylProd.measurePreserving_level (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w))
    (hf : ∀ v, Measurable (pf v)) {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1) :
    MeasurePreserving (fun x => (fun w => pa w x, fun v : S => pf v x)) (μ.restrict {x | ∀ v ∉ S, pf v x ∈ K v})
      ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)) := by
  classical
  have hπ : Measurable fun x => (fun w => pa w x, fun v : S => pf v x) :=
    (measurable_pi_lambda _ ha).prodMk (measurable_pi_lambda _ fun v => hf v)
  refine ⟨hπ, (prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (FiniteSpanningSetsIn.pi fun w => (μa w).toFiniteSpanningSetsIn)
    (FiniteSpanningSetsIn.pi fun v : S => (μf v).toFiniteSpanningSetsIn) ?_).symm⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hm := (MeasurableSet.univ_pi fun w => hA w (mem_univ _)).prod (MeasurableSet.univ_pi fun v => hB v (mem_univ _))
  have e := h.2 S hS A (fun v => if hv : v ∈ S then B ⟨v, hv⟩ else univ) (fun w => hA w (mem_univ _))
    fun v hv => by simp only [dif_pos hv]; exact hB ⟨v, hv⟩ (mem_univ _)
  rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm), Measure.pi_pi, Measure.pi_pi]
  convert e using 2
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, mem_setOf_eq, and_assoc, Subtype.forall]
    exact and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv => by rw [dif_pos hv]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]

variable (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w)) (hf : ∀ v, Measurable (pf v))
  (hK : ∀ v, MeasurableSet (K v))

include h ha hf hK

variable {𝕜 : Type} [RCLike 𝕜] {fa : ∀ w, Ya w → 𝕜} {ff : ∀ v, Yf v → 𝕜}

theorem IsCylProd.setIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, Integrable (fa w) (μa w))
    (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    IntegrableOn (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} μ ∧
    ∫ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  have hp := h.measurePreserving_level ha hf hS
  have hi := (Integrable.fintype_prod_dep hfa).mul_prod
    (Integrable.fintype_prod_dep (μ := fun v : S => μf v) fun v : S => hff v v.2)
  have e : EqOn (fun x => (∏ w, fa w (pa w x)) * ∏ v : S, ff v (pf v x))
      (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} := fun x hx => by
    simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]
  refine ⟨IntegrableOn.congr_fun (hp.integrable_comp_of_integrable hi) e (measurableSet_level hf hK S), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_level hf hK S) e, ← Finset.prod_coe_sort S,
    ← integral_fintype_prod_eq_prod, ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← hp.map_eq,
    integral_map hp.aemeasurable (hp.map_eq ▸ hi.aestronglyMeasurable)]

theorem IsCylProd.integral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ ∧
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  obtain ⟨hi, e⟩ := h.setIntegral_tensor ha hf hK hS
    (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff
  have h0 : ∀ x ∉ {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) = 0 := fun x hx => by
    rw [finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero h0, by rw [← e, setIntegral_eq_integral_of_forall_compl_eq_zero h0]⟩

end GlobalTheory.RestrMeas

namespace GlobalTheory.AdelicU

end GlobalTheory.AdelicU

end
