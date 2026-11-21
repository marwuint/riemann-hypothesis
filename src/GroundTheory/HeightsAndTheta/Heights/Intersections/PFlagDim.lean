import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagDimSt
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FlagDim

abbrev UIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2} ⊕ Fin (n - 1)

def uMat (F : Type) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (UIdx n) F) :=
  Matrix.of fun r c =>
    if h : r < c then X (Sum.inl ⟨(r, c), h⟩)
    else if h' : r = c ∧ r.val + 1 < n then X (Sum.inr ⟨r.val, by omega⟩) else 0

def toUpper (F : Type) [Field F] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) F →ₐ[F] MvPolynomial (UIdx n) F :=
  aeval fun p => uMat F n p.1 p.2

def flagMinorMap (F : Type) [Field F] (n : ℕ) :
    MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (Fin n × Fin n) F :=
  aeval fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2

section Trdeg

variable (F : Type) [Field F] (n : ℕ)

abbrev upperKer : Ideal (MRingOver F (PluckerBlocks n n)) := RingHom.ker ((toUpper F n).comp (flagMinorMap F n))

instance upperKer_isPrime : (upperKer F n).IsPrime := RingHom.ker_isPrime _

end Trdeg

end FlagDim

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
