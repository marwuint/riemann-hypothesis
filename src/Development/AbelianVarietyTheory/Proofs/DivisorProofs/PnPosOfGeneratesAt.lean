import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombForm

section Atlas

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def tAtlas (A : FinHolAtlas e X) (h : X ≃ₜ X') : FinHolAtlas e X' where
  n := A.n
  chart j := h.symm.transOpenPartialHomeomorph (A.chart j)
  cover x := (A.cover (h.symm x)).imp fun _ hj => hj
  holo j k := by
    have e₁ : (h.symm.transOpenPartialHomeomorph (A.chart k)) ∘ (h.symm.transOpenPartialHomeomorph (A.chart j)).symm =
        A.chart k ∘ (A.chart j).symm := funext fun y => by simp
    have e₂ : (h.symm.transOpenPartialHomeomorph (A.chart j)).target ∩
        (h.symm.transOpenPartialHomeomorph (A.chart j)).symm ⁻¹' (h.symm.transOpenPartialHomeomorph (A.chart k)).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      ext y; simp
    rw [e₁, e₂]
    exact A.holo j k

theorem tAtlas_symm (A : FinHolAtlas e X) (h : X ≃ₜ X') (j : Fin (tAtlas A h).n) (y : Fin e → ℂ) :
    ((tAtlas A h).chart j).symm y = h ((A.chart j).symm y) := rfl

end Atlas

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

section Met

variable {σ : F →+* ℂ} {Δ : Y.Dv}

end Met

end GlobalTheory.Mean4O.CombForm
