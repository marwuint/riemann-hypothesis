import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

noncomputable section

open MeasureTheory Matrix Ad3.K Ad3.K.LC

namespace GlobalTheory.CompanionTheory.GodementKFinC

def mnr (a b : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ := p.1 0 a * p.1 1 b - p.1 0 b * p.1 1 a

def qcj (c : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (starRingEnd ℂ) (p.2 0 * p.1 0 c + p.2 1 * p.1 1 c)

def gs (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * ((∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ))

def spM : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) :=
  Submodule.span ℂ {mnr 0 1, mnr 0 2, mnr 1 2}

def spQ : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) :=
  Submodule.span ℂ {qcj 0, qcj 1, qcj 2}

def spG : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) := Submodule.span ℂ {gs}

def spP (a b : ℕ) : Submodule ℂ (M23 × (Fin 2 → ℂ) → ℂ) := spM ^ a * spQ ^ b * spG

theorem spP_fg (a b : ℕ) : (spP a b).FG := by
  have h1 : spM.FG := Submodule.fg_span (by simp)
  have h2 : spQ.FG := Submodule.fg_span (by simp)
  have h3 : spG.FG := Submodule.fg_span (by simp)
  exact ((h1.pow a).mul (h2.pow b)).mul h3

instance spP_finiteDimensional (a b : ℕ) : FiniteDimensional ℂ (spP a b) :=
  Module.Finite.iff_fg.2 (spP_fg a b)

end GlobalTheory.CompanionTheory.GodementKFinC
