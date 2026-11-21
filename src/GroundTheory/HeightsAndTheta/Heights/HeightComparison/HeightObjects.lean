import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} {n : ι → ℕ}

abbrev blockIdx (n : ι → ℕ) : ι → Type := fun k ↦ Fin (n k + 1)

def flatCone {F : Type*} (z : Cone n F) : Coord n → F := fun p ↦ z p.1 p.2

def unflatCone {F : Type*} (w : Coord n → F) : Cone n F := fun k i ↦ w ⟨k, i⟩

@[simp] theorem unflatCone_flatCone {F : Type*} (z : Cone n F) : unflatCone (flatCone z) = z := rfl

@[simp] theorem flatCone_unflatCone {F : Type*} (w : Coord n → F) : flatCone (unflatCone w) = w := rfl

theorem blockNonzero_unflatCone_iff {F : Type*} [Zero F] (w : Coord n → F) :
    BlockNonzero (unflatCone w) ↔ ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 :=
  forall_congr' fun _ ↦ Function.ne_iff

theorem eval_map_flatCone {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    eval (flatCone z) (map (Int.castRingHom F) f) = evalCone z f := by
  rw [eval_map]
  rfl

variable [Fintype ι] [DecidableEq ι]

theorem weight_coordDeg_apply (d : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) d k = ∑ i, d ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [coordDeg]
  · intro j _ hj
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp [coordDeg, Pi.single_apply, Ne.symm hj]
  · simp

theorem geoMultiHomog_iff (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    Geo.IsMultiHomog (ι := blockIdx n) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_coordDeg_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_coordDeg_apply, h (mem_support_iff.mp hm)]

namespace HermLine

open Classical in

def toGeo (A : HermLine n) : Geo.HermLine (blockIdx n) where
  a := A.deg
  h w := if BlockNonzero (unflatCone w) then A.metric (unflatCone w) else 0
  pos w hw := by
    have hw' : BlockNonzero (unflatCone w) := (blockNonzero_unflatCone_iff w).mpr hw
    rw [if_pos hw']
    exact A.metric_pos _ hw'
  smul c w hc := by
    have e : unflatCone (fun p : Coord n ↦ c p.1 * w p) = fun k i ↦ c k * unflatCone w k i := rfl
    by_cases hw : BlockNonzero (unflatCone w)
    · have hcw : BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro k hk
        apply hw k
        funext i
        have := congrFun hk i
        rw [e] at this
        exact (mul_eq_zero.mp this).resolve_left (hc k)
      rw [if_pos hw, if_pos hcw, e, A.metric_smul c _ hc hw]
    · have hcw : ¬ BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro h
        apply hw
        intro k hk
        apply h k
        funext i
        rw [e]
        simp [congrFun hk i]
      rw [if_neg hw, if_neg hcw, mul_zero]

theorem toGeo_a (A : HermLine n) : A.toGeo.a = A.deg := rfl

theorem toGeo_h_of_blockNonzero (A : HermLine n) {w : Coord n → ℂ}
    (hw : BlockNonzero (unflatCone w)) : A.toGeo.h w = A.metric (unflatCone w) := by
  simp only [toGeo, if_pos hw]

end HermLine

namespace IntegralSection

end IntegralSection

def orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Geo.mCoordIdeal (ι := blockIdx n) (flatCone x)

theorem chartMonomial_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartMonomial c d ∉ orbitIdeal x := by
  intro h
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at h
  rw [chartMonomial, map_prod] at h
  refine (Finset.prod_ne_zero_iff.mpr fun k _ ↦ ?_) h
  rw [map_pow, Geo.mConeMap, aeval_X]
  exact pow_ne_zero _ (mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _))

theorem isSectionOn_chartMonomial (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ)
    (hd : ∀ k, A.deg k = d k) :
    Geo.IsSectionOn (orbitIdeal x) A.toGeo (chartMonomial c d) :=
  ⟨d, hd, (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    chartMonomial_notMem_orbitIdeal x c hc d⟩

theorem exists_chart {F : Type*} [Zero F] {x : Cone n F} (hx : BlockNonzero x) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, x k (c k) ≠ 0 :=
  ⟨fun k ↦ (Function.ne_iff.mp (hx k)).choose, fun k ↦ (Function.ne_iff.mp (hx k)).choose_spec⟩

def samplePoint : Cone (fun _ : Unit ↦ 1) (AlgebraicClosure ℚ) := fun _ ↦ ![1, 2]

end

end GroundTheory.Heights₂.Heights
