import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff

noncomputable section

namespace MultiProjectiveCoordinates.Val

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Small

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem mhb_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a) (hh : IsMultiHomog h b) :
    IsMultiHomog (g * h) (a + b) := by
  classical
  exact (Bridge.isMultiHomog_iff _ _).mp
    (IsWeightedHomogeneous.mul ((Bridge.isMultiHomog_iff _ _).mpr hg) ((Bridge.isMultiHomog_iff _ _).mpr hh))

omit [Fintype K] in
theorem mhb_add {g h : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (hh : IsMultiHomog h a) :
    IsMultiHomog (g + h) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h1 | h1
  exacts [hg m h1, hh m h1]

omit [Fintype K] in
theorem mhb_neg {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) : IsMultiHomog (-g) a := by
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

omit [Fintype K] in
theorem mhb_C (n : ℤ) : IsMultiHomog (C n : MRing ι) 0 := by
  classical
  exact (Bridge.isMultiHomog_iff _ _).mp (isWeightedHomogeneous_C _ _)

theorem mem_iff (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hg, mul_eq_zero, C_eq_zero]
  refine or_iff_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero _)

variable {𝕜 : Type} [Field 𝕜]

def V (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → 𝕜) (s : Ω) (w : 𝕜) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y g = s * aeval y h ∧ aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

omit [Fintype K] in
theorem V.hasVal {s : Ω} {w : 𝕜} (h : V y z s w) : HasVal y 0 s z w := by
  obtain ⟨d, g, h, a, b, c, e, f⟩ := h
  exact ⟨d, d, g, h, a, b, fun k => by simp, c, e, f⟩

theorem V.rep (hz : ∀ f ∈ mCoordIdeal y, aeval z f = 0) {s : Ω} {w : 𝕜} (hv : V y z s w) {d : K → ℕ}
    {g h : MRing ι} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) (e : aeval y g = s * aeval y h) :
    aeval z g = w * aeval z h := by
  obtain ⟨d', g', h', hg', hh', e', n', f'⟩ := hv
  have h1 : IsMultiHomog (g * h' + -(h * g')) (d + d') := mhb_add (mhb_mul hg hh') (mhb_neg (mhb_mul hh hg'))
  have h2 := hz _ ((mem_iff y h1).2 (by simp only [map_add, map_neg, map_mul, e, e']; ring))
  simp only [map_add, map_neg, map_mul, f'] at h2
  apply mul_right_cancel₀ n'
  linear_combination h2

theorem V.uniq (hz : ∀ f ∈ mCoordIdeal y, aeval z f = 0) {s : Ω} {w w' : 𝕜} (hv : V y z s w)
    (hv' : V y z s w') : w = w' := by
  obtain ⟨d, g, h, hg, hh, e, n, f⟩ := hv'
  exact mul_right_cancel₀ n ((hv.rep hz hg hh e).symm.trans f)

omit [Fintype K] in
theorem V.add {s t : Ω} {w x : 𝕜} (h1 : V y z s w) (h2 : V y z t x) : V y z (s + t) (w + x) := by
  obtain ⟨d, g, h, hg, hh, e, n, f⟩ := h1
  obtain ⟨d', g', h', hg', hh', e', n', f'⟩ := h2
  refine ⟨d + d', g * h' + h * g', h * h', mhb_add (mhb_mul hg hh') (mhb_mul hh hg'), mhb_mul hh hh', ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, e, e']; ring
  · rw [map_mul]; exact mul_ne_zero n n'
  · simp only [map_add, map_mul, f, f']; ring

omit [Fintype K] in
theorem V.mul {s t : Ω} {w x : 𝕜} (h1 : V y z s w) (h2 : V y z t x) : V y z (s * t) (w * x) := by
  obtain ⟨d, g, h, hg, hh, e, n, f⟩ := h1
  obtain ⟨d', g', h', hg', hh', e', n', f'⟩ := h2
  refine ⟨d + d', g * g', h * h', mhb_mul hg hg', mhb_mul hh hh', ?_, ?_, ?_⟩
  · simp only [map_mul, e, e']; ring
  · rw [map_mul]; exact mul_ne_zero n n'
  · simp only [map_mul, f, f']; ring

omit [Fintype K] in
theorem V.int (n : ℤ) : V y z (n : Ω) (n : 𝕜) :=
  ⟨0, C n, C 1, mhb_C _, mhb_C _, by simp, by simp, by simp⟩

omit [Fintype K] in
theorem V.rat [CharZero Ω] [CharZero 𝕜] (q : ℚ) : V y z (q : Ω) (q : 𝕜) := by
  refine ⟨0, C q.num, C (q.den : ℤ), mhb_C _, mhb_C _, ?_, ?_, ?_⟩
  · have : ((q.den : ℕ) : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp [Rat.cast_def, this]
  · simp
  · have : ((q.den : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast q.den_nz
    simp [Rat.cast_def, this]

end MultiProjectiveCoordinates.Val
