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
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSet

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem isNoetherian_of_locallyNoetherian_projOverField {F : Type} [Field F] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp F}
    (hproj : IsProjOver p) : AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨n, i, hi, hpi⟩ := hproj
  have := isProper_str F n
  have : IsProper p := hpi ▸ inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

theorem infinite_of_ringHom_complex {F : Type} [Field F] (σ : F →+* ℂ) : Infinite F := by
  haveI : CharZero F := σ.charZero
  exact Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective

theorem reciprocity_of_generated_right (hP : GlobalTheory.Published.Principalisation) (F : Type) [Field F] (X : Scheme.{0})
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ) (hproj : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t)
    (hcod : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t)
    (hN : ∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) =
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus t}
  have hS : S.Finite := (Set.finite_singleton _).union (_root_.GlobalTheory.Mix.finite_coheight_one_notMem_open X (nonzeroLocus t) ht)
  obtain ⟨A, hA, a, hAgen, hMAgen, haS⟩ := _root_.GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero F X p hproj M.B M.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ nonzeroLocus a :=
    fun z hz hzt => haS z (Or.inr ⟨hz, hzt⟩)
  obtain ⟨s₁, h₁, hloc, hadd⟩ := _root_.GlobalTheory.DefectAdd.defect_add hP F X p σ e hproj hdim L M A' N s hs a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩)
  have h0A := _root_.GlobalTheory.RecSec.reciprocity_sec hP F X p σ e hproj hdim L A' N a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl (haz z hz hzt)) hAgen hN
  have h0MA := _root_.GlobalTheory.RecSec.reciprocity_sec hP F X p σ e hproj hdim L (M.tens A') N s₁ h₁ t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · left
      rw [hloc]
      exact ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩) hMAgen hN
  linarith

theorem reciprocity_of_noCommonDivisor : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus s}
  have hS : S.Finite := (Set.finite_singleton _).union (_root_.GlobalTheory.Mix.finite_coheight_one_notMem_open X (nonzeroLocus s) hs)
  obtain ⟨A, hA, a, hAgen, hNAgen, haS⟩ := _root_.GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero F X p hproj N.B N.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus s → z ∈ nonzeroLocus a :=
    fun z hz hzs => haS z (Or.inr ⟨hz, hzs⟩)
  obtain ⟨t₁, h₁, hloc, hadd⟩ := _root_.GlobalTheory.DefectAdd.defect_add hP F X p σ e hproj hdim L N A' M t ht a ha s hs (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inr hzs
    · exact Or.inl ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩)
  have h0A := reciprocity_of_generated_right hP F X p σ e hproj hdim L M A' s hs a ha (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · exact Or.inr (haz z hz hzs)) hAgen
  have h0NA := reciprocity_of_generated_right hP F X p σ e hproj hdim L M (N.tens A') s hs t₁ h₁ (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · right
      rw [hloc]
      exact ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩) hNAgen
  linarith

end GlobalTheory.Mix
