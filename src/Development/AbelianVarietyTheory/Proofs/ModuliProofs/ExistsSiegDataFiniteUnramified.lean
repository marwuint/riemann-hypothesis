import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

end GlobalTheory.ZM.SiegClause
