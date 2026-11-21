import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitDict

section Partial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun f : Y → ℂ => f ∘ e) {f | f ∈ SB Y} {f | f ∈ SB X} := by
  refine ⟨fun f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩,
    fun f _ g _ hfg => ?_, fun g hg => ⟨g ∘ e.symm, ⟨hg.1.comp_continuous e.symm.continuous,
      hg.2.comp_homeomorph e.symm⟩, ?_⟩⟩
  · funext y
    simpa using congrFun hfg (e.symm y)
  · funext x
    simp

omit [DecidableEq n] [T2Space T] in

theorem exists_box_invariant_snd {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by
  obtain ⟨hlc, hcs⟩ := hf
  have hlc2 : IsLocallyConstant fun p : (T × (n → k)) × (n → k) => f (p.1.1, p.1.2 + p.2) - f p.1 :=
    (hlc.comp_continuous (by fun_prop)).sub (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
    hlc2.isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact (isCompact_singleton (x := (0 : n → k))) hW (by
    rintro ⟨z, u⟩ ⟨-, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu])
  obtain ⟨s, hs⟩ := exists_box_subset (hV.mem_nhds (h0V rfl))
  have key : ∀ z ∈ tsupport f, ∀ u ∈ box n s, f (z.1, z.2 + u) = f z := by
    intro z hz u hu
    have hm : (z, u) ∈ {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
      hUV ⟨hKU hz, hs hu⟩
    exact sub_eq_zero.mp hm
  refine ⟨s, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact key z hz u hu
  · by_cases hz' : (z.1, z.2 + u) ∈ tsupport f
    · have hneg : -u ∈ box n s := fun i _ => neg_mem_cball (hu i (Set.mem_univ i))
      have := key _ hz' (-u) hneg
      simp only [add_neg_cancel_right, Prod.mk.eta] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

omit [DecidableEq n] [T2Space T] [Fintype n] in
theorem slice_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t : T) :
    (fun x => f (t, x)) ∈ SB (n → k) := by
  haveI := t2Space k
  refine ⟨hf.1.comp_continuous (by fun_prop),
    HasCompactSupport.intro (hf.2.isCompact.image continuous_snd) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

def pf (ψ : AddChar k Circle) (μ : Measure (n → k)) (f : T × (n → k) → ℂ) : T × (n → k) → ℂ :=
  fun z => ∫ x, f (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ) ∂μ

private theorem exists_isOpen_nhd_eq_of_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ x, f (t, x) = f (t₀, x) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hW : IsOpen {p : T × (n → k) | f p - f (t₀, p.2) = 0} :=
    (hlc.sub (hlc.comp_continuous (by fun_prop))).isOpen_fiber 0
  obtain ⟨U, V, hU, -, ht₀U, hLV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := t₀))
    (hcs.isCompact.image continuous_snd) hW (by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      simp only [Set.mem_singleton_iff] at ht
      simp [ht])
  refine ⟨U, hU, ht₀U rfl, fun t ht x => ?_⟩
  by_cases hx : x ∈ Prod.snd '' tsupport f
  · have hm : (t, x) ∈ {p : T × (n → k) | f p - f (t₀, p.2) = 0} := hUV ⟨ht, hLV hx⟩
    exact sub_eq_zero.mp hm
  · have h1 : (t, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    have h2 : (t₀, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem pf_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) : pf ψ μ f ∈ SB (T × (n → k)) := by
  obtain ⟨s, hs⟩ := exists_box_invariant_snd hf
  have hslice : ∀ t, (fun y => ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) :=
    fun t => fourier_mem_SB μ h (slice_mem_SB hf t)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨t₀, y₀⟩
    obtain ⟨V, hV, ht₀, hVf⟩ := exists_isOpen_nhd_eq_of_mem_SB hf t₀
    obtain ⟨O, hO, hy₀, hOf⟩ := (IsLocallyConstant.iff_exists_open _).mp (hslice t₀).1 y₀
    refine ⟨V ×ˢ O, hV.prod hO, ⟨ht₀, hy₀⟩, ?_⟩
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have e1 : pf ψ μ f (t, y) = pf ψ μ f (t₀, y) := by
      simp only [pf]
      congr 1
      funext x
      rw [hVf t ht x]
    rw [e1]
    exact hOf y hy
  · haveI := t2Space k
    refine HasCompactSupport.intro
      ((hf.2.isCompact.image continuous_fst).prod (isCompact_box (c * s⁻¹))) ?_
    rintro ⟨t, y⟩ hty
    rw [Set.mem_prod, not_and_or] at hty
    rcases hty with ht | hy
    · have h0 : ∀ x, f (t, x) = 0 := fun x =>
        image_eq_zero_of_notMem_tsupport fun hx => ht ⟨_, hx, rfl⟩
      simp [pf, h0]
    · show ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0
      exact fourier_eq_zero_pi μ h (f := fun x => f (t, x)) (fun u hu x => hs u hu (t, x)) hy

theorem inversion_const (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => m)) ∂(Measure.pi fun _ => m) =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => m) h hf
  have hbox : ∀ r : kˣ, (Measure.pi fun _ : n => m).real (box n r) =
      (nabs k r * m.real (𝒪[k] : Set k)) ^ Fintype.card n := by
    intro r
    have hc := measureReal_cball m r
    simp only [Measure.real] at hc ⊢
    rw [box, Measure.pi_pi, ENNReal.toReal_prod, hc, Finset.prod_const, Finset.card_univ]
  have h1 : nabs k s * nabs k (c * s⁻¹) = nabs k c := by
    rw [nabs_mul k, mul_left_comm, ← nabs_mul k, mul_inv_cancel, nabs_one k, mul_one]
  have h2 : nabs k s * m.real (𝒪[k] : Set k) * (nabs k (c * s⁻¹) * m.real (𝒪[k] : Set k)) =
      m.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
    rw [← h1]; ring
  rw [hs, hbox, hbox, ← mul_pow, h2]

omit [T2Space T] in
theorem pf_pf (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (z : T × (n → k)) :
    pf ψ (Measure.pi fun _ => m) (pf ψ (Measure.pi fun _ => m) f) z =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f (z.1, -z.2) := by
  haveI := secondCountable k
  obtain ⟨t, y⟩ := z
  have hsl := slice_mem_SB hf t
  have hg : (fun w => f (t, w - y)) ∈ SB (n → k) :=
    ⟨hsl.1.comp_continuous (continuous_sub_right y), hsl.2.comp_homeomorph (Homeomorph.subRight y)⟩
  have hinv := inversion_const m h hg
  simp only [zero_sub] at hinv
  show ∫ x, (∫ w, f (t, w) * (ψ (w ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => m)) * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => m) = _ * f (t, -y)
  rw [← hinv]
  congr 1
  funext x
  rw [← integral_mul_const]
  have e := integral_sub_right_eq_self (μ := Measure.pi fun _ : n => m)
    (fun u => f (t, u) * (ψ ((u + y) ⬝ᵥ x) : ℂ)) y
  simp only [sub_add_cancel] at e
  rw [e]
  congr 1
  funext u
  rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm y x]
  ring

theorem pf_bijOn (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by
  haveI := secondCountable k
  set C : ℂ := (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) with hC
  have hC0 : C ≠ 0 := by
    have h1 : 0 < m.real (𝒪[k] : Set k) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero m ⟨0, by simp⟩)
        (isCompact_int k).measure_lt_top.ne
    have h2 := nabs_pos k c
    rw [hC]
    exact Complex.ofReal_ne_zero.mpr (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  have hsmul : ∀ (a : ℂ) (g : T × (n → k) → ℂ), pf ψ (Measure.pi fun _ : n => m) (a • g) = a • pf ψ (Measure.pi fun _ : n => m) g := by
    intro a g
    funext z
    simp only [pf, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hpp : ∀ g ∈ SB (T × (n → k)), ∀ z, pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g) z = C * g (z.1, -z.2) :=
    fun g hg z => pf_pf m h hg z
  refine ⟨fun g hg => pf_mem_SB (Measure.pi fun _ : n => m) h hg, fun g hg g' hg' hgg => ?_, fun g hg => ?_⟩
  · funext z
    have e1 := hpp g hg (z.1, -z.2)
    have e2 := hpp g' hg' (z.1, -z.2)
    rw [hgg] at e1
    simp only [neg_neg, Prod.mk.eta] at e1 e2
    exact mul_left_cancel₀ hC0 (e1.symm.trans e2)
  · have h2 := pf_mem_SB (Measure.pi fun _ : n => m) h (pf_mem_SB (Measure.pi fun _ : n => m) h hg)
    refine ⟨(C ^ 2)⁻¹ • pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g)), (SB _).smul_mem _ (pf_mem_SB (Measure.pi fun _ : n => m) h h2), ?_⟩
    rw [hsmul]
    funext z
    rw [Pi.smul_apply, hpp _ h2, hpp _ hg]
    simp only [neg_neg, Prod.mk.eta, smul_eq_mul]
    field_simp

end Partial

end GlobalTheory.SplitDict
