import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ld (X : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (X * g)

def Lw (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) : Mat n → V :=
  w.foldr (fun p h => Ld (bs p) h) f

@[simp] theorem Lw_nil (f : Mat n → V) : Lw [] f = f := rfl

theorem Lw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Lw (p :: w) f = Ld (bs p) (Lw w f) := rfl

end Ops

end GlobalTheory.CompanionTheory.WaveCp
