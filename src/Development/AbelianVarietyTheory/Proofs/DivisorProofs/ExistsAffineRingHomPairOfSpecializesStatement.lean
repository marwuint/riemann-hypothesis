import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes : ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X), RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  first | exact @GlobalTheory.exists_ringHom_pair_of_specializes | exact GlobalTheory.exists_ringHom_pair_of_specializes | (intros; apply GlobalTheory.exists_ringHom_pair_of_specializes <;> assumption)
