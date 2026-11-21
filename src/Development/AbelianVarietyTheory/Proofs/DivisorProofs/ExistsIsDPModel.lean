import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def tensorEval {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] (ψ : A →+* R) :
    R₀ ⊗[ℤ] A →ₗ[ℤ] R :=
  TensorProduct.lift ((LinearMap.mul ℤ R).compl₁₂ (algebraMap R₀ R).toAddMonoidHom.toIntLinearMap
    ψ.toAddMonoidHom.toIntLinearMap)

@[simp] theorem tensorEval_tmul {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R]
    (ψ : A →+* R) (r : R₀) (a : A) : tensorEval ψ (r ⊗ₜ a) = algebraMap R₀ R r * ψ a := rfl

end GlobalTheory.RealMult
