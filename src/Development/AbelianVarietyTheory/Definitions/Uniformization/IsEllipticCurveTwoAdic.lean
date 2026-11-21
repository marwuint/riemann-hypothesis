import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.SettingConsistentExample

theorem exists_even_one {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (P : CP G)
    (i : H ⟶ G) (hi : i = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  subst hi
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ := (PEmpty.elim : PEmpty → (H.left ⟶ G.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![(1 : H ⟶ G).left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ H.left) (z : Z) (J), Good P.L.L z J → val t r z J = 1 :=
    fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨t, ht, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, MonObj.comp_one, (isCub_cubV P.c hJ).face, _root_.mul_one]
  · show val t _ z J = _ * val t _ z J
    rw [v _ _ z J hJ, v _ _ z J hJ, MonObj.comp_one, P.val_sym_one hJ, _root_.mul_one]

section Generic
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

variable (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (X : Type) [AddCommGroup X] [Subsingleton X]

omit hG' in
theorem ab_even (P : CP G) : ∃ σ : CubTriv P.c (TQ.abelian G hG X).i, σ.Even :=
  exists_even_one _ _ (Hom.one_def).symm

end Generic

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

def curveTwoAdic : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩

instance isElliptic_curveTwoAdic : curveTwoAdic.IsElliptic := ⟨by
  have h : curveTwoAdic.Δ = -(3 : ℤ_[2]) ^ 3 := by
    simp only [curveTwoAdic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have h3 : IsUnit (3 : ℤ_[2]) := by
    have : ‖((3 : ℕ) : ℤ_[2])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.2 (by norm_num)
    exact PadicInt.isUnit_iff.2 (by simpa using this)
  rw [h]
  exact (h3.pow 3).neg⟩

end GlobalTheory.UU.SettingConsistentExample
end
