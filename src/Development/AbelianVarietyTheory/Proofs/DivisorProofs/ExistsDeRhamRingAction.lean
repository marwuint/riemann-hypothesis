import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.DRAct

section Pull

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} (κ : DividedPowers I) (t : S ⟶ Sp R)
  {A : Over S} [GrpObj A]

theorem primPull_of_eq_id (f : A ⟶ A) [IsMonHom f] (h : f = 𝟙 A) (c : prim κ t A) : primPull κ t f c = c := by
  subst h
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem primPull_of_eq_comp (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f ≫ g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f (primPull κ t g c) := by
  subst h
  exact (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c).symm

theorem primPull_of_eq_mul (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f * g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f c + primPull κ t g c := by
  subst h
  exact Subtype.ext (c.2 A f g)

end Pull

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] (i : OAct O A)

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

end GlobalTheory.AbDatum.DRAct

