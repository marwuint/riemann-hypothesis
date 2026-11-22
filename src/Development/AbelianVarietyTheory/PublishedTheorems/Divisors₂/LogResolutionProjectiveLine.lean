import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution

namespace GlobalTheory

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt

namespace Published

def AnalyticLogResolution : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A →
  ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
  ∀ (q : ℕ) (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ),
    (∀ i, IsPotential A (L i) ∧ IsSection A (L i) (t i) ∧ ∃ y ∈ Z, t i y y ≠ 0) →
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : CompactSpace Y) (_ : T2Space Y) (B : FinHolAtlas n Y)
    (μ : Y → X) (_ : HoloMap B A μ) (S : Set X) (r : ℕ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ)
    (J : Finset (Fin r)),
    IsProjective B ∧ Set.range μ = Z ∧ A.IsAnalyticSubset S ∧ Z \ S ⊆ regularLocus A Z n ∧
    Z ⊆ closure (Z \ S) ∧ Set.InjOn μ (μ ⁻¹' S)ᶜ ∧
    (∀ y, y ∉ μ ⁻¹' S → ∀ j, y ∈ (B.chart j).source → ∀ v : Fin n → ℂ,
      fderiv ℂ (fun w => A.chart (chartIdx A (μ y)) (μ ((B.chart j).symm w))) (B.chart j y) v = 0 →
        v = 0) ∧
    μ ⁻¹' S = ⋃ k ∈ J, W k ∧ IsJointSNC B μ L t W e

end Published

namespace AnLogRes

end AnLogRes

end GlobalTheory
