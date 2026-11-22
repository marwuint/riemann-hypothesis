import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ZariskiConn

theorem fibre_preconnected : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ z : Z, _root_.IsPreconnected (π.base ⁻¹' {z}) := by
  intro Y Z π _ _ _ _ hN U hU hiso z
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hS := _root_.GlobalTheory.ZariskiSections.bijective_appTop_restrict Y Z π hN U hU hiso V hV
  haveI : IsAffine (V : Scheme) := hV
  have hC := _root_.GlobalTheory.ZariskiConn.isPreconnected_fibre (V : Scheme) (π ⁻¹ᵁ V) (π ∣_ V) hS ⟨z, hzV⟩
  have key : π.base ⁻¹' {z} = (π ⁻¹ᵁ V).ι.base '' ((π ∣_ V).base ⁻¹' {⟨z, hzV⟩}) := by
    ext y
    constructor
    · intro hy
      have hy' : π.base y = z := hy
      have hyV : y ∈ π ⁻¹ᵁ V := by
        show π.base y ∈ V
        rw [hy']; exact hzV
      refine ⟨⟨y, hyV⟩, ?_, rfl⟩
      show (π ∣_ V).base ⟨y, hyV⟩ = ⟨z, hzV⟩
      exact Subtype.ext ((morphismRestrict_base_coe π V ⟨y, hyV⟩).trans hy')
    · rintro ⟨w, hw, rfl⟩
      have hw' : (π ∣_ V).base w = ⟨z, hzV⟩ := hw
      exact (morphismRestrict_base_coe π V w).symm.trans (congrArg Subtype.val hw')
  rw [key]
  exact hC.image _ (π ⁻¹ᵁ V).ι.base.hom.continuous.continuousOn

end GlobalTheory.ZariskiConn
