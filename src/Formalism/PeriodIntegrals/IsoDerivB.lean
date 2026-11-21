import Mathlib

noncomputable section

namespace PI.IsoDerivB

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev VC (T : Type) (N N' : ℕ) : Type := T → Fin N' → Fin N → ℂ

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

end PI.IsoDerivB
