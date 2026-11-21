import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.WachLatticeTwists.HodgeTateChains.GammaIterateMatrixCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
open scoped TensorProduct

section prod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

def Phi (W : NData S ι pr D) (x : ι → D) : ι → D := fun i => W.φ i (x (pr i))

end prod

def galT {ℓ : ℕ} [Fact ℓ.Prime] {WC : Type} [CommRing WC] [Algebra ℤ_[ℓ] WC] {Gg : Type} [Group Gg]
    (act : Gg →* (WC ≃+* WC)) {r : ℕ} (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (g : Gg)
    (v : Fin r → WC) : Fin r → WC :=
  (fun j => act g (v j)) ᵥ* (ρ g).map (algebraMap ℤ_[ℓ] WC)

structure Cmp {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (jA : As →+* AA) (io : AA →+* WC) (φ : WC →+* WC)
    {Gg : Type} [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC)) {r : ℕ}
    (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) where
  cmp : (ι → D) →+ (Fin r → WC)
  smul : ∀ (a : As) (x : ι → D), cmp (jS a • x) = io (jA a) • cmp x
  phi : ∀ x, cmp (Phi W x) = fun j => φ (cmp x j)
  fixH : ∀ h ∈ H, ∀ x, galT act ρ h (cmp x) = cmp x

end Formalism.RepresentationBoundsCohomology.JW
