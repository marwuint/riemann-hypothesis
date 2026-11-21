import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d

def linVal (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroLocus J ∧ A *ᵥ x = w}

def withFirst (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ) :
    Fin (e + 1) → (Fin n → ℂ) → ℝ :=
  Fin.cons (α := fun _ => (Fin n → ℂ) → ℝ) f ψ

def SmoothNear (Z : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U, IsOpen U ∧ Z ⊆ U ∧ ContDiffOn ℝ ∞ f U

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
