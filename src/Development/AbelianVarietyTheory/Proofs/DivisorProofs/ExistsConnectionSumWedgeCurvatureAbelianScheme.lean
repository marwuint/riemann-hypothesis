import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationPairingWellDefined
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationSemilinearPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem dRel_pO {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : Y ⟶ A) (x : HO1 A.hom) {n : ℕ}
    (y : Fin n → HO1 A.hom) (w : Fin n → GlobForm A.hom) (h : DRel (OAff A.hom) x y w) :
    DRel (OAff Y.hom) (pO1 f x) (fun k ↦ pO1 f (y k)) (fun k ↦ pF f (w k)) :=
  _root_.GlobalTheory.dRel_pull R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) x n y w h

theorem sum_dRel_eq_zero (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) (x : HO1 A.hom) {n : ℕ} (y : Fin n → HO1 A.hom)
    (w : Fin n → GlobForm A.hom) (hx : DRel (OAff A.hom) x y w) (l : GlobForm A.hom →ₗ[R] R) :
    ∑ k, l (w k) • y k = 0 := by
  obtain ⟨-, -, hA2, hs2⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨hax, hafF, -⟩ := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  have hprim := _root_.GlobalTheory.AbCoh.primO1_of_isAbelianScheme R A g hA hs x
  set a₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set a₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  have hμ := dRel_pO μ[A] x y w hx
  have hfst := dRel_pO (fst A A) x y w hx
  have hsnd := dRel_pO (snd A A) x y w hx
  have hsum := (_root_.GlobalTheory.AbCoh.rel_add R _ (OAff (A ⊗ A).hom)).1 _ _ _ _ _ _ _ _ hfst hsnd
  rw [← hprim] at hsum
  have key := _root_.GlobalTheory.AbCoh.derivClass_eq R _ (OAff (A ⊗ A).hom) hF2 hC2 _ _ _ _ _ _ _ hμ hsum (l ∘ₗ pF a₂)
  rw [Fin.sum_univ_add] at key
  simp only [LinearMap.comp_apply, Fin.append_left, Fin.append_right] at key
  have e1 : ∀ k, l (pF a₂ (pF μ[A] (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.2]
  have e2 : ∀ k, l (pF a₂ (pF (fst A A) (w k))) = 0 := fun k ↦ by rw [(hafF (w k)).2.2.2.1, map_zero]
  have e3 : ∀ k, l (pF a₂ (pF (snd A A) (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.1]
  simp only [e1, e2, e3, zero_smul, Finset.sum_const_zero, zero_add] at key
  have := congrArg (pO1 a₁) key
  simp only [map_sum, map_smul] at this
  have f1 : ∀ k, pO1 a₁ (pO1 μ[A] (y k)) = y k := fun k ↦ (hax (y k)).2.2.1
  have f2 : ∀ k, pO1 a₁ (pO1 (snd A A) (y k)) = 0 := fun k ↦ (hax (y k)).2.1
  simp only [f1, f2, smul_zero, Finset.sum_const_zero] at this
  exact this

theorem exists_obRel_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, ∃ (m : ℕ) (u v : Fin m → GlobForm A.hom),
      ObRel (OAff A.hom) x u v := by
  intro R _ A _ g hA hs x
  obtain ⟨hF, hC, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  obtain ⟨n, y, w, hx⟩ := GlobalTheory.T.exists_cohomologyDerivativeRelation_of_frame R _ (OAff A.hom) hF x
  exact _root_.GlobalTheory.AbCoh.exists_obRel_of_dRel R _ (OAff A.hom) hF hC x n y w hx
    (fun l ↦ sum_dRel_eq_zero R A g hA hs x y w hx l)

end GlobalTheory.AbCoh
