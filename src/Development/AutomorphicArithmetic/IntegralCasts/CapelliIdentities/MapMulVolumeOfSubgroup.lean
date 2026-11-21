import Mathlib

open MeasureTheory Set

private noncomputable def mulE {n : ℕ} (a x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  Matrix.of.symm (Matrix.of a * Matrix.of x)

private lemma mulE_apply {n : ℕ} (a x : Fin n → Fin n → ℂ) (i j : Fin n) :
    mulE a x i j = ∑ k, a i k * x k j := by
  simp [mulE, Matrix.mul_apply]

private lemma continuous_mulE {n : ℕ} :
    Continuous (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => mulE p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulE_apply]
  fun_prop

private lemma measurable_mulE {n : ℕ} (a : Fin n → Fin n → ℂ) : Measurable (mulE a) :=
  (continuous_mulE.comp (Continuous.prodMk_right a)).measurable

private lemma haarE (n : ℕ) :
    (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure ℂ)
  exact Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure (Fin n → ℂ))

private lemma mulE_cancel {n : ℕ} {a y v w : Fin n → Fin n → ℂ} (ha : (Matrix.of a).det ≠ 0)
    (h : mulE (mulE a y) v = mulE a w) : mulE y v = w := by
  have hu : IsUnit (Matrix.of a) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit ha)
  have h' : Matrix.of a * (Matrix.of y * Matrix.of v) = Matrix.of a * Matrix.of w := by
    rw [← Matrix.mul_assoc]
    exact h
  exact hu.mul_left_cancel h'

private lemma key {n : ℕ} {G : Set (Fin n → Fin n → ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
    [SFinite μ] (hG : μ Gᶜ = 0) (hdet : ∀ a ∈ G, (Matrix.of a).det ≠ 0)
    (hvol : ∀ a ∈ G, Measure.map (mulE a) volume = volume)
    (hinv : ∀ a ∈ G, Measure.map (mulE a) μ = μ)
    {V K B D : Set (Fin n → Fin n → ℂ)} (hV : IsCompact V) (hB : IsCompact B)
    (hD : MeasurableSet D)
    (hK : ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K)
    (hBD : ∀ g ∈ B, ∀ v ∈ V, mulE g v ∈ D) :
    volume V * μ B ≤ μ K * volume D := by
  set S : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    (fun p => (p.1, mulE p.1 p.2)) '' (B ×ˢ V) with hS
  have hSm : MeasurableSet S :=
    ((hB.prod hV).image (continuous_fst.prodMk continuous_mulE)).measurableSet
  have hae : ∀ᵐ g ∂μ, g ∈ G := hG
  have h1 : volume V * μ B ≤ (μ.prod volume) S := by
    rw [Measure.prod_apply hSm, ← lintegral_indicator_const hB.measurableSet]
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hgB : g ∈ B
    · rw [indicator_of_mem hgB]
      have hm : MeasurableSet (Prod.mk g ⁻¹' S) := measurable_prodMk_left hSm
      calc volume V ≤ volume (mulE g ⁻¹' (Prod.mk g ⁻¹' S)) :=
            measure_mono fun v hv => ⟨(g, v), ⟨hgB, hv⟩, rfl⟩
        _ = volume (Prod.mk g ⁻¹' S) := by
            rw [← Measure.map_apply (measurable_mulE g) hm, hvol g hg]
    · rw [indicator_of_notMem hgB]
      exact zero_le
  have h2 : (μ.prod volume) S ≤ μ K * volume D := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const hD]
    refine lintegral_mono fun x => ?_
    have hm : MeasurableSet ((fun g => (g, x)) ⁻¹' S) := measurable_prodMk_right hSm
    by_cases hne : (((fun g => (g, x)) ⁻¹' S) ∩ G).Nonempty
    · obtain ⟨a, ⟨⟨a', w⟩, ⟨haB, hw⟩, he⟩, haG⟩ := hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      show μ _ ≤ _
      rw [indicator_of_mem (hBD _ haB _ hw), ← hinv _ haG,
        Measure.map_apply (measurable_mulE _) hm, hinv _ haG]
      refine measure_mono ?_
      rintro y ⟨⟨g, v⟩, ⟨-, hv⟩, he'⟩
      obtain ⟨rfl, h'⟩ := Prod.mk.inj he'
      exact hK y v hv w hw (mulE_cancel (hdet _ haG) h')
    · have : μ ((fun g => (g, x)) ⁻¹' S) = 0 :=
        measure_mono_null (fun g hg hgG => hne ⟨g, hg, hgG⟩) hG
      show μ _ ≤ _
      rw [this]
      exact zero_le
  exact h1.trans h2

