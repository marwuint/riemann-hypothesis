import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilPhi

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory GlobalTheory.PDivGroup GlobalTheory.CartierDual

section Level

variable {O : Type} [CommRing O] {A B : Type} [CommRing A] [CommRing B]

section Alg

variable [Algebra O A] [Algebra O B]

def ev (y : A →ₐ[O] O) (x : B →ₐ[O] O) : A ⊗[O] B →ₐ[O] O :=
  Algebra.TensorProduct.lift y x fun _ _ => Commute.all _ _

@[simp] theorem ev_tmul (y : A →ₐ[O] O) (x : B →ₐ[O] O) (a : A) (b : B) :
    ev y x (a ⊗ₜ b) = y a * x b := rfl

end Alg

variable [HopfAlgebra O A] [Module.Finite O A] [Module.Projective O A]

structure IsBimul (u : A ⊗[O] A) : Prop where
  one_left : ∀ x : A →ₐ[O] O, ev (1 : WithConv (A →ₐ[O] O)).ofConv x u = 1
  one_right : ∀ x : A →ₐ[O] O, ev x (1 : WithConv (A →ₐ[O] O)).ofConv u = 1
  mul_left : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev (y * y').ofConv x u = ev y.ofConv x u * ev y'.ofConv x u
  mul_right : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev x (y * y').ofConv u = ev x y.ofConv u * ev x y'.ofConv u

variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C]
  {u : A ⊗[O] A} (h : IsBimul u)

include C h

end Level

end GlobalTheory.WeilPhi

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.WeilPhi

end GlobalTheory.WeilPhi
