import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

def OverSub {AA WC : Type} [CommRing AA] [CommRing WC] (ι : AA →+* WC) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) WC) : Prop := ∃ M' : Matrix (Fin r) (Fin r) AA, M'.map ι = M

structure HypW (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ) where

  Xx : Matrix (Fin r) (Fin r) WC

  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1

  fixH : ∀ h ∈ H, Xx.map (act h) * ((ρ h : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC)) = Xx

  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx

  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P

  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC))
    = ((Gm g).map jA).map ι * Xx

  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}

  W4 : ∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ], (∀ g, E * (ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = ρ g * E) →
    ∃ E' : Matrix (Fin r) (Fin r) As, Xx * E.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

def LemmaAProp {AA WC : Type} [CommRing AA] [CommRing WC] (ι : AA →+* WC) (φ : WC →+* WC) (r : ℕ) :
    Prop :=
  ∀ Z S S' Y : Matrix (Fin r) (Fin r) WC, OverSub ι S → OverSub ι S' → OverSub ι Y →
    Z.map φ = S * Z * S' + Y → OverSub ι Z

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
