module

public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {Z : X.IdealSheafData}
  {E : List X.IdealSheafData}

theorem hasStrictNormalCrossingsWith_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    HasStrictNormalCrossingsWith (π ≫ p) (Blowup.exceptionalIdeal π Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [Blowup.exceptionalIdeal_eq_comap] at hx
  have hy : π.base x ∈ Z.support := by
    simp only [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
  refine ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m,
    (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact fun i hi => absurd hi (Nat.not_lt_zero i)
  · exact BlowupChart.restrictIdeal_exceptionalIdeal
      (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU

theorem isSmoothDivisor_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    IsSmoothDivisor (π ≫ p) (Blowup.exceptionalIdeal π Z) := by
  have hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p)) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) []
      (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact (isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩

private theorem smooth_ι_comp_of_etaleChart {Y : Scheme.{u}} {K : Type u}
    [Field K] {q : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (c : EtaleChart q V n) :
    Smooth (V.ι ≫ q) := by
  have := c.isEtale
  have hsm : Smooth c.map := inferInstance
  have hsa : Smooth (affineSpaceFinToSpec K n) := affineSpaceIsSmooth K n
  rw [← c.comp_struct]
  infer_instance

theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Smooth (π ≫ p) := by
  have key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p)) := by
    intro x
    by_cases hxs : π.base x ∈ Z.support
    · obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
      have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
      obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
      exact ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB,
        smooth_ι_comp_of_etaleChart (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩
    · refine ⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩
      have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
        Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
      have h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) =
          AlgebraicGeometry.morphismRestrict π Z.support.compl ≫
            (Scheme.Opens.ι Z.support.compl ≫ p) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      rw [h1]
      infer_instance
  choose U hU hsm using key
  have hUtop : iSup U = ⊤ := by
    rw [eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm

end FunctorialResolution.EmbeddedResolution
