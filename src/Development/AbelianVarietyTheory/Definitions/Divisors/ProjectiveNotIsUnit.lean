import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

structure Charts {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) where

  D : ∀ e, Fin (n + 1) → (Y e).left.Opens

  aff : ∀ e i, IsAffineOpen (D e i)

  cover : ∀ e, ⨆ i, D e i = ⊤

  pre : ∀ e i, β e ⁻¹ᵁ D (e + 1) i = D e i

  ρ : ∀ e i, Fin (n + 1) → Γ((Y e).left, D e i)

  ρ_pull : ∀ e i j, ((β e).appLE (D (e + 1) i) (D e i) (pre e i).ge).hom (ρ (e + 1) i j) = ρ e i j

  ρ_self : ∀ i, ρ 0 i i = 1

  basic : ∀ i j, (Y 0).left.basicOpen (ρ 0 i j) = D 0 i ⊓ D 0 j

  cocycle : ∀ i j l, rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i l) =
    rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i j) *
      rs (Y 0).left (inf_le_right : D 0 i ⊓ D 0 j ≤ D 0 j) (ρ 0 j l)

  surj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (cst (Y 0).hom (D 0 i)) (ρ 0 i))

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

def towerIdeal (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (J : Ideal R)
    (V : (Y e).left.Opens) : Ideal Γ((Y e).left, V) :=
  J.map (cst ((Y e).hom ≫ thick R I e) V)

def Charts.ev (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+* Γ((Y e).left, C.D e i) :=
  MvPolynomial.eval₂Hom (cst ((Y e).hom ≫ thick R I e) (C.D e i)) (C.ρ e i)

@[simp] theorem Charts.ev_X (C : Charts I Y β n) (e : ℕ) (i j : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X j) = C.ρ e i j := by
  rw [Charts.ev]
  exact MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem Charts.ev_C (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) (r : R) :
    C.ev e i (MvPolynomial.C r) = cst ((Y e).hom ≫ thick R I e) (C.D e i) r := by
  rw [Charts.ev]
  exact MvPolynomial.eval₂Hom_C _ _ _

end GlobalTheory.FormalAlg
