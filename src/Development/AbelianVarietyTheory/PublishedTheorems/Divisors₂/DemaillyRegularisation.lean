import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg

namespace GlobalTheory.Published

def IsPshExt {d : ℕ} (U : Set (Fin d → ℂ)) (v : (Fin d → ℂ) → EReal) : Prop :=
  (∀ z ∈ U, v z ≠ ⊤) ∧ UpperSemicontinuousOn v U ∧ U ⊆ closure {z ∈ U | v z ≠ ⊥} ∧
    ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh U fun z => (max (v z) ((-κ : ℝ) : EReal)).toReal

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

def IsClosedForm (R : AnRead p σ d) (θ : ChartForm p σ d) : Prop := ∀ y, ∃ W φ, y ∈ W ∧ IsPotential R θ W φ

def IsFormPsh (R : AnRead p σ d) (θ : ChartForm p σ d) (v : CxPts p σ → EReal) : Prop :=
  ∀ W φ, IsPotential R θ W φ → ∀ c : AlgChart p σ d,
    IsPshExt (c.finChart.target ∩ c.finChart.symm ⁻¹' W) fun z => ((φ (c.finChart.symm z) : ℝ) : EReal) + v (c.finChart.symm z)

def DemaillyRegularisation : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p],
    CompactSpace (CxPts p σ) → T2Space (CxPts p σ) →
    ∀ (a θ : ChartForm p σ d) (E : ChartMap p σ d) (v : CxPts p σ → EReal),
      IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → IsClosedForm (AnRead.all p σ d) θ →
      IsFormPsh (AnRead.all p σ d) θ v →
      ∃ A K δ : ℝ, IsRegConst a θ (rho a E fun y => (v y).toReal) A K δ ∧
        (∀ y, ∀ t ∈ Ioo 0 δ, v y ≤ ((rho a E (fun y => (v y).toReal) y t + K * t ^ 2 : ℝ) : EReal)) ∧
        ∀ y, Tendsto (fun t => ((rho a E (fun y => (v y).toReal) y t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (v y))

end GlobalTheory.Published

end
