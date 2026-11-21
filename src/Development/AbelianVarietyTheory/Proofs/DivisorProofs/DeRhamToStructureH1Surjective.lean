import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumWedgeWellDefinedAndDeRhamLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionCurvatureSumWedgeSemilinearPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_append {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem toHO1_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toHO1 A.hom) := by
  intro R _ A _ g hA hg x
  obtain ⟨m, u, v, hx⟩ := _root_.GlobalTheory.AbCoh.exists_obRel_abelian R A g hA hg x
  obtain ⟨-, -, hAA, hgAA⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hg
  have hcl : Closed1 (OAff (A ⊗ A).hom) = ⊤ := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R (A ⊗ A) (g + g) hAA hgAA
  have hμ := _root_.GlobalTheory.AbCoh.obRel_pullHO1 R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) x m u v hx
  have h1 := _root_.GlobalTheory.AbCoh.obRel_pullHO1 R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) x m u v hx
  have h2 := _root_.GlobalTheory.AbCoh.obRel_pullHO1 R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) x m u v hx
  have hsum := (_root_.GlobalTheory.AbCoh.rel_add R _ (OAff (A ⊗ A).hom)).2.1 _ _ m m _ _ _ _ h1 h2
  have hprim : pullHO1 (ovw μ[A]) x = pullHO1 (ovw (fst A A)) x + pullHO1 (ovw (snd A A)) x :=
    _root_.GlobalTheory.AbCoh.primO1_of_isAbelianScheme R A g hA hg x
  rw [← hprim] at hsum
  have heq := (_root_.GlobalTheory.AbCoh.curvature_wellDefined_and_lift R _ (OAff (A ⊗ A).hom)).1 hcl _ m (m + m) _ _ _ _ hμ hsum
  rw [wsum_append] at heq
  have h0 : wsum (OAff A.hom) u v = 0 := _root_.GlobalTheory.AbCoh.wsum_eq_zero_of_mul R A g hA hg m u v heq
  exact (_root_.GlobalTheory.AbCoh.curvature_wellDefined_and_lift R _ (OAff A.hom)).2 x m u v hx h0

end GlobalTheory.AbCoh
