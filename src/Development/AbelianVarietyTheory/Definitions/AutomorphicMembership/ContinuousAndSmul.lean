import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix MeasureTheory Set Complex
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ChernReg

section Flat

variable {d : ℕ}

def polMat (q : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ := fun k l =>
  (q (Pi.single k 1 + Pi.single l 1) - q (Pi.single k 1 - Pi.single l 1) +
    I * q (Pi.single k 1 + I • Pi.single l 1) - I * q (Pi.single k 1 - I • Pi.single l 1)) / 4

def christoffel (b : V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : V d) : V d :=
  WithLp.toLp 2 ((ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ) ᵥ* (b z)⁻¹)

def jet (b : V d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : V d × V d → V d :=
  n.rec Prod.fst fun _ f q => del f q (q.2, -christoffel b q.1 q.2)

variable (b : V d → Matrix (Fin d) (Fin d) ℂ)

theorem jet_zero : jet b 0 = Prod.fst := rfl

theorem jet_succ (n : ℕ) (q : V d × V d) : jet b (n + 1) q = del (jet b n) q (q.2, -christoffel b q.1 q.2) := rfl

def cutoff (t : ℝ) : ℝ := if t < 1 then ((1 - t) ^ 2)⁻¹ * Real.exp (t - 1)⁻¹ else 0

def mean (q f : (Fin d → ℂ) → ℝ) : ℝ := (∫ ξ, f ξ * cutoff (q ξ)) / ∫ ξ, cutoff (q ξ)

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

abbrev ChartMap (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → CxPts p σ

def matIn (a : ChartForm p σ d) (c : AlgChart p σ d) (v : V d) : Matrix (Fin d) (Fin d) ℂ := polMat (a c (c.e.symm v))

structure IsExph (a : ChartForm p σ d) (E : ChartMap p σ d) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ContinuousOn (fun q : V d × V d => E c (c.e.symm q.1) q.2.ofLp) (c.e.target ×ˢ univ)

  smooth : ∀ c c' : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × V d => c'.e (E c (c.e.symm q.1) q.2.ofLp))
    {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c'.e.source}

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (ξ : V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

def ConjComm (j : CxPts p σ' → CxPts p σ) (E : ChartMap p σ d) (E' : ChartMap p σ' d) : Prop :=
  ∀ (c : AlgChart p σ d) (c' : AlgChart p σ' d),
    (∀ w ∈ c'.e.source, j w ∈ c.e.source → ∀ i, c'.e w i = starRingEnd ℂ (c.e (j w) i)) →
    ∀ z ∈ c'.e.source, j z ∈ c.e.source → ∀ ξ, j (E' c' z ξ) = E c (j z) (star ξ)

def rhoIn (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) : ℝ :=
  mean (a c y) fun ξ => ψ (E c y (t • ξ))

structure IsRegConst (a θ : ChartForm p σ d) (Ψ : CxPts p σ → ℝ → ℝ) (A K δ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  K_nonneg : 0 ≤ K
  δ_pos : 0 < δ
  smooth : ∀ c : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖)
    (c.e.target ×ˢ {w | 0 < ‖w‖ ∧ ‖w‖ < δ})
  mono : ∀ y, MonotoneOn (fun t => Ψ y t + K * t ^ 2) (Ioo 0 δ)
  hess : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → ∀ (ξ : V d) (η : ℂ),
    -(A * (‖w‖ * deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
        K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
      θ c y ξ.ofLp + (leviForm (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

variable {a : ChartForm p σ d} {E : ChartMap p σ d} {R : AnRead p σ d}

variable [SmoothOfRelativeDimension d p]

def rho (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) (t : ℝ) : ℝ :=
  rhoIn a E ψ (AlgChart.exists_mem_source (D := d) y).choose y t

end Manifold

end GlobalTheory.ChernReg
