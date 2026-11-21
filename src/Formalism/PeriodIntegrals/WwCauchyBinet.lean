import Mathlib

noncomputable section

namespace PI.WwCauchyBinet

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwCauchyBinet : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (k : Type) [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k),
    DeX N nu y = ∑ᶠ J : KM.ColChoice N nu, MvPolynomial.C (minY N nu J y) *
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)

end PI.WwCauchyBinet
