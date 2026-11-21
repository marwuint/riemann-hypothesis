import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalGenericDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem map_mem_map_iff {W : Ideal (MRing ι)} (hW : W.IsPrime) (hh : IsHorizontal W) (x : MRing ι) :
    MvPolynomial.map (Int.castRingHom ℚ) x ∈ W.map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ x ∈ W := by
  classical
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = MvPolynomial.map (Int.castRingHom ℚ) := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hdisj : Disjoint (S : Set (MRing ι)) W := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmW
    have h0 : m ∈ W.comap (C : ℤ →+* MRing ι) := hmW
    rw [hh, Ideal.mem_bot] at h0
    exact zero_notMem_nonZeroDivisors (h0 ▸ hm)
  have h := IsLocalization.under_map_of_isPrime_disjoint S (MRingOver ℚ ι) hW hdisj
  constructor
  · intro hx
    rw [← h]
    show algebraMap (MRing ι) (MRingOver ℚ ι) x ∈ Ideal.map (algebraMap (MRing ι) (MRingOver ℚ ι)) W
    rw [hφ]
    exact hx
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

theorem isMultiHomog_map [DecidableEq K] {x : MRing ι} {e : K → ℕ} (h : NumbersDVR.IsMultiHomog x e) :
    NumbersDVR.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℚ) x) e := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end VerticalGenericDeg

end GroundTheory.Heights₂.Heights.NineStatements
