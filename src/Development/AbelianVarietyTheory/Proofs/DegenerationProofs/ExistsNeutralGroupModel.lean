import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLaw
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLaw
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := _root_.GlobalTheory.SS.WeakNeronEx.exists_weakNeron R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := _root_.GlobalTheory.SS.NeutralModel.exists_birLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := _root_.GlobalTheory.SS.exists_strict_le R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := _root_.GlobalTheory.SS.exists_grpObj_of_strict R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
