import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.ChartFun

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

abbrev res (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) : Γ(M, W) →+* Γ(M, W') :=
  (M.presheaf.map (homOfLE hle).op).hom

def chartMap (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] :
    Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
  (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom.comp (res M hle)

end GlobalTheory.RealMult.ChartFun
