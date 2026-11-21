import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementDS

noncomputable section

namespace PI.BesselPeriodGGP

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

section Defs

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ

def IsQuotMeas (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  ∀ f : Formalism.QuantumDeterminants.Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def IsSPsiEquiv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : Prop :=
  ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    W (h * m * g) = ψ m • π h (W g)

def l2SG {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : ENNReal :=
  ∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν

def rconv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp :=
  fun x => ∫ g, e (Matrix.of g) • W (x * Matrix.of g) ∂μG

def fdegH (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG

def eFun (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  (fdegH μG σ w : ℂ) * star ⟪w, σ g w⟫_ℂ

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Defs

end PI.BesselPeriodGGP
