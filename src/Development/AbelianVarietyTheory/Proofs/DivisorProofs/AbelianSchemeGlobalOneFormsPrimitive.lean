import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (_root_.GlobalTheory.AbCoh.fp_ext_prod).2 R _ _ g g (_root_.GlobalTheory.AbCoh.globForm_FP R A g hA hs) (_root_.GlobalTheory.AbCoh.globForm_FP R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := _root_.GlobalTheory.AbCoh.globForm_FP R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add, map_add, h1, k2, h4, k5, add_zero, zero_add]
  have hbij := _root_.GlobalTheory.AbCoh.bijective_of_split_of_FP R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
