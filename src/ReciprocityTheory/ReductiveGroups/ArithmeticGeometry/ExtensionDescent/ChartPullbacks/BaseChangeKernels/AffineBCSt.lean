import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

def AffineBCSt : Prop :=
  ∀ {G B G' B' : Scheme.{0}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B},
    IsPullback g q' q b → IsAffineHom q → ∀ {X : Type} [AddCommMonoid X]
    {V : B.Opens}, IsAffineOpen V → ∀ {V' : B'.Opens}, IsAffineOpen V' →
    V' ≤ b ⁻¹ᵁ V → ∀ (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V')),
    (∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _))

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
