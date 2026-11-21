import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeSqrtMulSum

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ldp (X : Mat n) (K : Mat n × Mat n → V) : Mat n × Mat n → V := fun p => fderiv ℝ K p (0, X * p.2)

def Hw (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) : Mat n × Mat n → V :=
  w.foldr (fun p h => Ldp (bs p) h) K

@[simp] theorem Hw_nil (K : Mat n × Mat n → V) : Hw [] K = K := rfl

theorem Hw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (K : Mat n × Mat n → V) :
    Hw (p :: w) K = Ldp (bs p) (Hw w K) := rfl

def fld (X : Mat n) : (Mat n × Mat n) →L[ℝ] (Mat n × Mat n) :=
  (ContinuousLinearMap.inr ℝ (Mat n) (Mat n)).comp ((GlobalTheory.CompanionTheory.RCalc.mulL X).comp (ContinuousLinearMap.snd ℝ (Mat n) (Mat n)))

theorem fld_apply (X : Mat n) (p : Mat n × Mat n) : fld X p = (0, X * p.2) := rfl

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
