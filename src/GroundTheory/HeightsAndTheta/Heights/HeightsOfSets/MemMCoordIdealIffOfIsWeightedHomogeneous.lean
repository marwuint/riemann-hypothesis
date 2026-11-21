import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveIsOrbit
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem mConeMap_monomial {Ω : Type*} [Field Ω] (y : Coord n → Ω) (d : Coord n →₀ ℕ) (c : ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (monomial d c) =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d))
        (aeval y (monomial d c)) := by
  rw [Geo.mConeMap, aeval_monomial, aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ d p =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d)) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ d ⟨k, i⟩ = _
    show _ = (X k : MvPolynomial ι Ω) ^ (Finsupp.weight (coordDeg n) d k)
    rw [Finset.prod_pow_eq_pow_sum, weight_coordDeg_apply]
  rw [hX, MvPolynomial.algebraMap_apply, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]

theorem mConeMap_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    Geo.mConeMap (ι := blockIdx n) y g =
      monomial (Finsupp.equivFunOnFinite.symm m) (aeval y g) := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [mConeMap_monomial, hg (mem_support_iff.mp hd)]

theorem mem_mCoordIdeal_iff_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y g = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isWeightedHomogeneous y hg, monomial_eq_zero]

def compDegs (f : MvPolynomial (Coord n) ℤ) : Finset (ι → ℕ) :=
  (weightedHomogeneousComponent_finsupp (w := coordDeg n) f).toFinset

omit [Fintype ι] in

theorem sum_compDegs (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ compDegs f, weightedHomogeneousComponent (coordDeg n) m f = f := by
  rw [compDegs, ← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f),
    sum_weightedHomogeneousComponent]

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem_mCoordIdeal {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) :
    aeval y f = 0 := by
  have key : ∀ g : MvPolynomial (Coord n) ℤ,
      eval (fun _ ↦ (1 : Ω)) (Geo.mConeMap (ι := blockIdx n) y g) = aeval y g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p v hp =>
      rw [map_mul, map_mul, hp, map_mul]
      simp [Geo.mConeMap]
  rw [← key, Geo.mCoordIdeal, RingHom.mem_ker] at *
  rw [hf, map_zero]

theorem mem_mCoordIdeal_iff {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔
      ∀ m, aeval y (weightedHomogeneousComponent (coordDeg n) m f) = 0 := by
  classical
  constructor
  · intro hf m₀
    by_cases h0 : weightedHomogeneousComponent (coordDeg n) m₀ f = 0
    · rw [h0, map_zero]
    have hm₀ : m₀ ∈ compDegs f := (Set.Finite.mem_toFinset _).mpr h0
    have hk := congrArg (coeff (Finsupp.equivFunOnFinite.symm m₀))
      (show Geo.mConeMap (ι := blockIdx n) y f = 0 from hf)
    rw [← sum_compDegs f, map_sum, coeff_sum, coeff_zero,
      Finset.sum_eq_single m₀] at hk
    · rwa [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m₀ f), coeff_monomial, if_pos rfl] at hk
    · intro m _ hm
      rw [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m f), coeff_monomial, if_neg]
      exact fun h ↦ hm (Finsupp.equivFunOnFinite.symm.injective h)
    · exact fun h ↦ absurd hm₀ h
  · intro h
    rw [← sum_compDegs f]
    refine Ideal.sum_mem _ fun m _ ↦ ?_
    exact (mem_mCoordIdeal_iff_of_isWeightedHomogeneous y
      (weightedHomogeneousComponent_isWeightedHomogeneous m f)).mpr (h m)

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_flatCone {F : Type*} [CommRing F] (x : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    aeval (flatCone x) f = evalCone x f := by
  rw [aeval_def, algebraMap_int_eq]
  rfl

theorem mem_orbitIdeal_iff_of_isWeightedHomogeneous (x : Cone n (AlgebraicClosure ℚ))
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ orbitIdeal x ↔ evalCone x g = 0 := by
  rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hg, aeval_flatCone]

theorem mem_points_iff_le_orbitIdeal (P : ArithVariety n) (x : Cone n (AlgebraicClosure ℚ)) :
    x ∈ P.points (AlgebraicClosure ℚ) ↔ BlockNonzero x ∧ P.ideal ≤ orbitIdeal x := by
  refine and_congr Iff.rfl ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [orbitIdeal, mem_mCoordIdeal_iff]
    intro m
    rw [aeval_flatCone]
    exact h _ (P.homogeneous f hf m)
  · rw [← aeval_flatCone]
    exact aeval_eq_zero_of_mem_mCoordIdeal _ (h hf)

theorem zariskiDense_iff_orbitIdeal (P : ArithVariety n) (S : Set (Cone n (AlgebraicClosure ℚ))) :
    P.ZariskiDense S ↔ Geo.IsZariskiDense (ι := blockIdx n) P.ideal (orbitIdeal '' S) := by
  constructor
  · rintro h f ⟨a, ha⟩ hfP
    by_contra hne
    have ha' := (geoMultiHomog_iff f a).mp ha
    refine hfP (h a f ha' fun z hz ↦ ?_)
    refine (mem_orbitIdeal_iff_of_isWeightedHomogeneous z ha').mp ?_
    by_contra hz'
    exact hne ⟨_, ⟨z, hz, rfl⟩, hz'⟩
  · intro h m f hf hvan
    by_contra hfP
    obtain ⟨W, ⟨z, hz, rfl⟩, hfW⟩ := h f ⟨m, (geoMultiHomog_iff f m).mpr hf⟩ hfP
    exact hfW ((mem_orbitIdeal_iff_of_isWeightedHomogeneous z hf).mpr (hvan z hz))

namespace HermLine

omit [DecidableEq ι] in
theorem ofGeo_deg (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) :
    (ofGeo B hB).deg = B.a := rfl

omit [DecidableEq ι] in
theorem ofGeo_metric (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) (z : Cone n ℂ) :
    (ofGeo B hB).metric z = B.h (flatCone z) := rfl

end HermLine

section Curves

variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]

omit [∀ k, Fintype (κ k)] in

theorem ptsIntegral_congr (P : Ideal (Geo.MRing κ)) {e : ℕ} (φ : Fin e → ((Σ k, κ k) → ℂ) → ℝ)
    {g g' : ((Σ k, κ k) → ℂ) → ℝ} (hg : ∀ z ∈ Geo.mcPts P, g z = g' z) :
    Geo.ptsIntegral P φ g = Geo.ptsIntegral P φ g' := by
  unfold Geo.ptsIntegral Geo.ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold Geo.sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec
      unfold Geo.IsSheet at hs
      congr 1
      exact hg _ hs.2.self_of_nhds.2.1
    · rfl
  · rfl

omit [∀ k, Fintype (κ k)] in

theorem arInt_congr (P : Ideal (Geo.MRing κ)) (s : Geo.MRing κ) {e : ℕ}
    (L : Fin e → Geo.HermLine κ) {A A' : Geo.HermLine κ}
    (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) : Geo.arInt P s A L = Geo.arInt P s A' L := by
  unfold Geo.arInt
  exact ptsIntegral_congr P _ fun z hz ↦ by rw [Geo.logNorm, Geo.logNorm, hh z hz]

omit [∀ k, Fintype (κ k)] in

theorem recR_congr (I : Ideal (Geo.MRing κ) → (m : ℕ) → (Fin m → Geo.HermLine κ) → ℝ)
    (P : Ideal (Geo.MRing κ)) {e : ℕ} (L : Fin e → Geo.HermLine κ) (s : Geo.MRing κ)
    {A A' : Geo.HermLine κ} (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) :
    Geo.recR I P L A s = Geo.recR I P L A' s := by
  unfold Geo.recR
  rw [arInt_congr P s L hh]

end Curves

namespace IntegralSection

end IntegralSection

end

end GroundTheory.Heights₂.Heights
