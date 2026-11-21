import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDerivSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_isSecBasis (x : Ix κ → Ω) (n : ℕ) :
    ∃ b : Fin (finrank ℤ (sec ℤ x n)) → MvPolynomial (Ix κ) ℚ, IsSecBasis x n b := by
  classical
  haveI : Module.Finite ℤ (sec ℤ x n) := by
    rw [Module.finite_def, Submodule.fg_top]
    exact (homogeneousSubmodule_fg (Ix κ) ℤ n).map _
  haveI : Module.Free ℤ (sec ℤ x n) := Module.free_of_finite_type_torsion_free'
  let bas := Module.finBasis ℤ (sec ℤ x n)
  have hmem : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ aeval x f = ((bas k : sec ℤ x n) : Ω) := by
    intro k
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (bas k).2
    exact ⟨f, (mem_homogeneousSubmodule n f).1 hf, hfx⟩
  choose f hfh hfx using hmem
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  have hval : (fun k => aeval x (map (Int.castRingHom ℚ) (f k))) = (sec ℤ x n).subtype ∘ bas := by
    funext k
    rw [hcast, hfx]
    rfl
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), fun k => ⟨f k, hfh k, rfl⟩, ?_, ?_⟩
  · rw [hval]
    exact bas.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  · rw [hval, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]

theorem IsSecBasis.card_eq {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : r = finrank ℤ (sec ℤ x n) := by
  rw [← hb.2.2, finrank_span_eq_card hb.2.1, Fintype.card_fin]

theorem continuousOn_rho {J : Type} [Fintype J] {m : ConeMetric ℂ J} (hm : IsSmoothMetric m) :
    ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz

theorem integrable_secFun {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (i j : Fin r) :
    Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ := by
  classical
  have hm : IsSmoothMetric m := hg.semipos.1
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  haveI : IsProbabilityMeasure μ := hg.vol.1
  have hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := by
    rw [ae_iff]
    exact hg.vol.2.1
  have hbound : ∀ k, ∃ C : ℝ, ∀ z : Ix κ → ℂ, z ≠ 0 → ‖secFun (b k) z‖ ^ 2 * wgt m n z ≤ C := by
    intro k
    have hdeg : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 →
        ‖secFun (b k) (c • z)‖ ^ 2 * wgt m n (c • z) = ‖secFun (b k) z‖ ^ 2 * wgt m n z := by
      intro c z hc
      have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
      have hpow : ‖c‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
      simp only [wgt]
      rw [secFun_smul (hb.1 k), m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖c‖), mul_inv, ← pow_mul]
      field_simp
      ring
    have hcont : ContinuousOn (fun z => ‖secFun (b k) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
      refine ContinuousOn.mul ?_ ?_
      · exact ((continuous_secFun (b k)).norm.pow 2).continuousOn
      · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'
    have hS : IsCompact (Metric.sphere (0 : Ix κ → ℂ) 1) := isCompact_sphere 0 1
    have hSsub : Metric.sphere (0 : Ix κ → ℂ) 1 ⊆ {0}ᶜ := by
      intro z hz h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hz
      exact zero_ne_one hz
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hcont.mono hSsub)
    refine ⟨C, fun z hz => ?_⟩
    have hnz : ((‖z‖ : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hz)
    have h1 := hdeg _ z hnz
    have hz1 : ((‖z‖ : ℝ) : ℂ)⁻¹ • z ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
    have h2 := hC _ hz1
    rw [← h1]
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h2)
  obtain ⟨Ci, hCi⟩ := hbound i
  obtain ⟨Cj, hCj⟩ := hbound j
  have hρm : Measurable m.ρ := by
    have h := ContinuousOn.measurable_piecewise hρ
      (by rw [compl_compl]; exact continuousOn_singleton m.ρ 0)
      (measurableSet_singleton (0 : Ix κ → ℂ)).compl
    rwa [Set.piecewise_same] at h
  have hw : Measurable (wgt m n) := (hρm.pow_const _).inv
  have hF : Measurable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) :=
    ((Complex.continuous_conj.comp (continuous_secFun (b i))).mul (continuous_secFun (b j))).measurable.mul
      (Complex.measurable_ofReal.comp hw)
  refine Integrable.mono' (integrable_const ((Ci + Cj) / 2)) hF.aestronglyMeasurable ?_
  filter_upwards [hpts] with z hz
  have hz0 : z ≠ 0 := hz.1
  have hwz : 0 ≤ wgt m n z := inv_nonneg.2 (pow_nonneg (m.pos z hz0).le _)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwz, Complex.norm_conj]
  have e1 := hCi z hz0
  have e2 := hCj z hz0
  nlinarith [mul_nonneg (sq_nonneg (‖secFun (b i) z‖ - ‖secFun (b j) z‖)) hwz]

theorem sum_secFun_smul {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) (a : ℂ) (w : Ix κ → ℂ) :
    ∑ i, c i * secFun (b i) (a • w) = a ^ n * ∑ i, c i * secFun (b i) w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secFun_smul (hb i)]
  ring

theorem isDegZero_normSq {m : ConeMetric ℂ (Ix κ)} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) : IsDegZero fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z := by
  intro a z ha
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hpow : ‖a‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
  simp only [wgt]
  rw [sum_secFun_smul hb, m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖a‖), mul_inv, ← pow_mul]
  field_simp
  ring

theorem continuousOn_normSq {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) {n r : ℕ}
    (b : Fin r → MvPolynomial (Ix κ) ℚ) (c : Fin r → ℂ) :
    ContinuousOn (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  refine ContinuousOn.mul ?_ ?_
  · exact ((continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_secFun (b i))).norm.pow 2).continuousOn
  · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'

theorem linIndep_rat_of_isSecBasis {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : LinearIndependent ℚ fun k => aeval x (b k) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.2.1

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
