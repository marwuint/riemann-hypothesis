import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Frame

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def eps (p : Bool × Fin n × Fin n) (A : Mat n) : ℝ :=
  if p.1 then (A p.2.1 p.2.2).re else (A p.2.1 p.2.2).im

theorem contDiff_eps (p : Bool × Fin n × Fin n) : ContDiff ℝ ∞ (eps p : Mat n → ℝ) := by
  obtain ⟨b, i, j⟩ := p
  cases b
  · have e : (eps (false, i, j) : Mat n → ℝ) = Complex.imCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.imCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)
  · have e : (eps (true, i, j) : Mat n → ℝ) = Complex.reCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.reCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)

theorem sum_eps (A : Mat n) : ∑ p, eps p A • (bs p : Mat n) = A := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, eps, bs, Matrix.sum_apply, Matrix.smul_apply]
  simp [Matrix.single_apply, Finset.sum_add_distrib, ite_and]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_dom : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) :=
  isOpen_univ.prod GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs

end GlobalTheory.CompanionTheory.WaveCp.Frame
