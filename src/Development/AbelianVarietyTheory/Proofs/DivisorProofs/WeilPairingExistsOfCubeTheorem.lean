import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt GlobalTheory.CartierDual WithConv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilHom

section Alg

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

section Values

variable [Algebra R A] [Algebra R B] {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]

def ev (x : A →ₐ[R] D) (z : B →ₐ[R] D) : A ⊗[R] B →ₐ[R] D :=
  Algebra.TensorProduct.lift x z fun _ _ => Commute.all _ _

@[simp] theorem ev_tmul (x : A →ₐ[R] D) (z : B →ₐ[R] D) (a : A) (b : B) : ev x z (a ⊗ₜ b) = x a * z b := rfl

end Values

variable [Bialgebra R A] [Bialgebra R B]

structure IsBimul (u : A ⊗[R] B) : Prop where

  isUnit : IsUnit u

  mul_left : ∀ (D : Type) [CommRing D] [Algebra R D] (x x' : WithConv (A →ₐ[R] D)) (z : B →ₐ[R] D),
    ev (x * x').ofConv z u = ev x.ofConv z u * ev x'.ofConv z u

  mul_right : ∀ (D : Type) [CommRing D] [Algebra R D] (x : A →ₐ[R] D) (z z' : WithConv (B →ₐ[R] D)),
    ev x (z * z').ofConv u = ev x z.ofConv u * ev x z'.ofConv u

variable [Module.Finite R B] [Module.Projective R B] {u : A ⊗[R] B} (h : IsBimul u)

end Alg

end GlobalTheory.WeilHom
