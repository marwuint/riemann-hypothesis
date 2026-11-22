import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := _root_.GlobalTheory.cxPts_var_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := _root_.GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
