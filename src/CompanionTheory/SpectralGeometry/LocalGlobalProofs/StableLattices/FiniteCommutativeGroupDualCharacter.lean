import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KerPull.Cartier

section Alg

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [Bialgebra k D] [Module.Finite k D]

abbrev Du := WithConv (Module.Dual k D)

variable {k D} {R : Type} [CommRing R]

def pair (a : D → R) (β : Du k D → R) : R :=
  ∑ i, a (Module.finBasis k D i) * β (toConv ((Module.finBasis k D).coord i))

variable [Algebra k R]

end Alg

section Sch

open scoped TensorProduct
open Coalgebra WithConv

def fnR {X : Scheme.{0}} {A : Type} [CommRing A] (x : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ x.appTop).hom

variable {k : Type} [Field k]

variable {D : Type} [CommRing D] [HopfAlgebra k D]

end Sch

section Aff

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [HopfAlgebra k D]

abbrev GD : Over (Sp k) := (Spec (.of D)).asOver (Spec (.of k))

variable [Module.Finite k D] [IsCocomm k D]

abbrev TE : Over (Sp k) := (Spec (.of (Du k D))).asOver (Spec (.of k))

variable {k D}

def P {W : Over (Sp k)} (x : W ⟶ GD k D) (t : W ⟶ TE k D) : Γ(W.left, ⊤) :=
  pair (fnR x.left) (fnR t.left)

end Aff

end GlobalTheory.CompanionTheory.KerPull.Cartier
