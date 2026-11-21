import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finite_coheight_one_notMem_open : ∀ (X : Scheme.{0}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U →
    {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  intro X _ _ U hU
  classical
  obtain ⟨S, hS, hc, hi, hUn⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun z hz => ?_
  obtain ⟨hz1, hzU⟩ := hz
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.1 (hUn.le (show z ∈ (U : Set X)ᶜ from hzU))
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint X := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint X := (Specializes.antisymm e (genericPoint_specializes _)).eq
    have hm : (hi T hT).genericPoint ∈ (U : Set X)ᶜ := hUn.ge (mem_sUnion.2 ⟨T, hT, hg.mem⟩)
    exact hm (e' ▸ hU)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Mix
