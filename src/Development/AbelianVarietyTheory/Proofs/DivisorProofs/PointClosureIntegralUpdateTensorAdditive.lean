import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix.CycAdd

theorem isProjOver_clos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p) (z : X) :
    IsProjOver (closι z ≫ p) := by
  obtain ⟨N, i, hi, h⟩ := hp
  exact ⟨N, closι z ≫ i, inferInstance, by rw [Category.assoc, h]⟩

theorem int_congr {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L M : Fin D → MLine p σ} (h : ∀ ε, part L ε = part M ε) (f : CxPts p σ → ℝ) : Mix.int L f = Mix.int M f := by
  simp only [Mix.int, h]

theorem pull_update {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (i : Fin D) (A : MLine p σ) (z : X) :
    (fun j => (Function.update L i A j).pull (closι z) rfl) =
      Function.update (fun j => (L j).pull (closι z) rfl) i (A.pull (closι z) rfl) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end GlobalTheory.Mix.CycAdd

open GlobalTheory.Mix.CycAdd in

theorem GlobalTheory.Mix.cycInt_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  intro k _ X p σ hp D L i A B f z hA hB
  have hq := isProjOver_clos hp z
  have hI := _root_.GlobalTheory.Mix.isom_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl
  have hparts : ∀ ε, part (fun j => (Function.update L i (A.tens B) j).pull (closι z) rfl) ε =
      part (Function.update (fun j => (L j).pull (closι z) rfl) i
        ((A.pull (closι z) rfl).tens (B.pull (closι z) rfl))) ε := by
    intro ε
    refine _root_.GlobalTheory.Mix.part_eq_of_isom k (clos z) (closι z ≫ p) σ hq D _ _ (fun j => ?_) ε
    by_cases hj : j = i
    · subst hj; simpa using hI.2.2.1 A B
    · simpa [Function.update_of_ne hj] using (_root_.GlobalTheory.Mix.isom_calculus k (clos z) (clos z) (closι z ≫ p) (closι z ≫ p) σ (𝟙 _) (Category.id_comp _)).1 ((L j).pull (closι z) rfl)
  unfold CycIntg at hA hB
  unfold cycInt
  rw [int_congr hparts, pull_update, pull_update]
  rw [pull_update] at hA hB
  exact (_root_.GlobalTheory.Mix.int_update_tens k (clos z) (closι z ≫ p) σ hq D _ i _ _ _ hA hB).2
