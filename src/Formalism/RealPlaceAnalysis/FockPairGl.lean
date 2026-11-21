import Formalism.RealPlaceAnalysis.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.REAL

def fockF {σ : Type*} (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

def sgnv {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') : Bool :=
  ε i == ε' a

def bop {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then (pderiv (i, a)).toLinearMap
  else LinearMap.mulLeft ℂ (X (i, a))

def bpl {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then LinearMap.mulLeft ℂ (X (i, a))
  else -(pderiv (i, a)).toLinearMap

def Eg {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  ∑ a, bpl ε ε' i a * bop ε ε' j a

def Eg' {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (a b : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  -∑ i, bpl ε ε' i b * bop ε ε' i a

def CCR : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a b : Fin n'),
    bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a = (if i = j ∧ a = b then 1 else 0) ∧
    bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a ∧
    bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a

def FockPairGl : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool),
    GlRel (Eg ε ε') ∧ GlRel (Eg' ε ε') ∧
    ∀ (i j : Fin M) (a b : Fin n'), Eg ε ε' i j * Eg' ε ε' a b = Eg' ε ε' a b * Eg ε ε' i j

end Formalism.REAL
