import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianUnobstructed_of_struct (hO : GlobalTheory.AbCoh.OStr)
    (hF : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧
        GlobalTheory.AbCoh.PrimF A) : GlobalTheory.Published.AbelianUnobstructed := by
  have hS : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b := by
    intro R _ A _ g hA hg
    obtain ⟨h1, h2, -, -⟩ := hO R A g hA hg
    exact ⟨h1, h2⟩
  exact GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension (_root_.GlobalTheory.Obs.unobDim_of_formSt (GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames hF) (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish hS))
    (_root_.GlobalTheory.Obs.axesE1_of_axesO1 (GlobalTheory.T.axesO1_of_projective_rank_cup hS)))

end GlobalTheory
