import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParamete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DoubleClassExtension

theorem two_smul_extends : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  intro S _ _ hS A _ hA U V hU hV c hc
  haveI : Smooth A.hom := hA.smooth
  haveI : GeometricallyConnected A.hom := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  haveI : GlobalTheory.IsNormalScheme S := GlobalTheory.IsNormalScheme.of_pred hS
  haveI : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hbig := _root_.GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one A.left S A.hom V U hV hU
  obtain ⟨Y, x, a, v, p, e, _, hxs, hxsurj, hpv, hmem, hsm2, hgi2, he⟩ := _root_.GlobalTheory.ParamTriple.exists_param S A hA V hV
  haveI := hxs
  haveI := hxsurj
  have h2 := _root_.GlobalTheory.pull_two_nsmul_eq_zero_of_triples S hS A hA U V (A.hom ⁻¹ᵁ U ⊔ V) le_sup_right hU hV le_sup_left le_rfl c hc
    Y x a v p e hpv hmem hsm2 hgi2 he
  haveI : GlobalTheory.IsNormalScheme Y.left := GlobalTheory.isNormalScheme_of_smooth x.left
  have hbigY := _root_.GlobalTheory.FlatCodimOne.preimage_contains_codim_le_one A.left Y.left x.left _ hbig
  have hloc := _root_.GlobalTheory.LocalTriv.locally_trivial A.left Y.left x.left (GlobalTheory.IsNormalScheme.pred _) _ hbigY (2 • c) h2
  exact _root_.GlobalTheory.extend_class_of_locally_trivial A.left (GlobalTheory.IsNormalScheme.pred _) _ hbig (2 • c) hloc

end GlobalTheory.DoubleClassExtension
