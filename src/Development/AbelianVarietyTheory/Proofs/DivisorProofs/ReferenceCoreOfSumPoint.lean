import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RefSum.primeSum_add_pair {S : Finset ℕ} {e : ℕ → ℝ} {s : ℝ} (h : PrimeSum S e s) (g : Fin 2 → ℕ)
    (hg : ∀ k, (g k).Prime) :
    PrimeSum (S ∪ Finset.univ.image g) (fun q => e q + if q ∈ Finset.univ.image g then 1 else 0)
      (s + (Real.log (g 0) + Real.log (g 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => ?_, fun q => add_nonneg (h2 q) (by split_ifs <;> norm_num), fun q hq => ?_, ?_⟩
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact h1 q hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hg k
  · rw [Finset.mem_union, not_or] at hq
    simp only [h3 q hq.1, if_neg hq.2, add_zero]
  · have a : ∑ q ∈ S ∪ Finset.univ.image g, e q * Real.log q = ∑ q ∈ S, e q * Real.log q :=
      (Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]).symm
    have b : ∑ q ∈ S ∪ Finset.univ.image g, (if q ∈ Finset.univ.image g then (1 : ℝ) else 0) * Real.log q =
        ∑ q ∈ Finset.univ.image g, Real.log q := by
      rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq, one_mul]
    have c : ∑ q ∈ Finset.univ.image g, Real.log (q : ℕ) ≤ ∑ k : Fin 2, Real.log (g k) :=
      Finset.sum_image_le_of_nonneg (f := fun q : ℕ => Real.log q) fun q _ => Real.log_natCast_nonneg q
    rw [Fin.sum_univ_two] at c
    simp only [add_mul, Finset.sum_add_distrib]
    linarith

