import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree

section Eigen

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]

def IsEigVec (act : OAct O G) (χ : O →+* R) (v : epsR R ⟶ G) : Prop :=
  IsTangent v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis (act : OAct O G) (χ : O →+* R) {m : ℕ} (v : Fin m → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsEigVec act χ (v i)) ∧ ∀ w, IsEigVec act χ w → ∃! c : Fin m → R, IsLieComb c v w

end Eigen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lines

variable {L : Type} [Field L] [NumberField L]

def ordIdeal (τ : E →+* L) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  FractionalIdeal.count L 𝔭
    ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def ordTwist (H : Host E) (τ : E →+* L) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  (ordIdeal τ (differentIdeal ℤ (𝓞 E)) 𝔭 - ordIdeal τ (Ideal.span {H.rt}) 𝔭) - ordIdeal τ (Ideal.span {H.rt}) 𝔭

end Lines

def IsHostField (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})

end GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree
