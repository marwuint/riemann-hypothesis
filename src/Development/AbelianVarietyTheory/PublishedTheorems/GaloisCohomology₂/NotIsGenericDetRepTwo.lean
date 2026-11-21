import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.Whittaker

section Generic

variable {R : Type} [CommRing R] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def superDiag (g : GL (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, (g : Matrix (Fin n) (Fin n) R) i j

def IsFunctional (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) (l : Module.Dual ℂ V) : Prop :=
  ∀ u ∈ unipB R (Fin n), ∀ v, l (π u v) = (ψ (superDiag u) : ℂ) * l v

def IsGeneric (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) : Prop :=
  ∃ l : Module.Dual ℂ V, l ≠ 0 ∧ IsFunctional ψ π l

end Generic

end GlobalTheory.Whittaker

namespace GlobalTheory.Published

namespace JacquetShalikaLocalBound

end JacquetShalikaLocalBound

end GlobalTheory.Published
