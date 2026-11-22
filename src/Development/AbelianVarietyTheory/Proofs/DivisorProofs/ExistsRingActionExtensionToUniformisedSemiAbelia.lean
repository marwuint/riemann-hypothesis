import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointGenericFibreOfActsStar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oLinear_of_oAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have L1 : ∀ a : O, ∃ g : G ⟶ G, IsMonHom g ∧ ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
    intro a
    obtain ⟨f, hf, hfA⟩ := _root_.GlobalTheory.Mum.GenericEnd.main R hR D A G hG U O o a
    obtain ⟨g, hg, hgf⟩ := _root_.GlobalTheory.Mum.genericEnd_extends R hR G hG (U.gen.hom ≫ f ≫ U.gen.inv) inferInstance
    refine ⟨g, hg, hfA g hg ?_⟩
    rw [hgf]; simp
  have L2 := _root_.GlobalTheory.Mum.actsAs_unique R hR D A G hG U
  choose g hg hgA using L1
  have one : g 1 = 𝟙 G := by
    refine L2 _ _ _ _ (hg 1) inferInstance (hgA 1) ?_
    have := actsAs_id U.toUnifPre
    rw [o.onB.map_one]
    convert this using 1
    funext χ; simp
  have mul : ∀ a b : O, g (a * b) = g b ≫ g a := by
    intro a b
    haveI := hg a; haveI := hg b
    refine L2 _ _ _ _ (hg (a * b)) inferInstance (hgA (a * b)) ?_
    have := actsAs_comp U.toUnifPre (hgA b) (hgA a)
    rw [o.onB.map_mul]
    convert this using 1
    funext χ; simp [star_mul, mul_smul]
  have add : ∀ a b : O, g (a + b) = padd G (g a) (g b) := by
    intro a b
    haveI := hg a; haveI := hg b
    have hp : IsMonHom (padd G (g a) (g b)) := by unfold padd; infer_instance
    refine L2 _ _ _ _ (hg (a + b)) hp (hgA (a + b)) ?_
    have := actsAs_padd U.toUnifPre (hgA a) (hgA b)
    rw [o.onB.map_add]
    convert this using 1
    funext χ; simp [star_add, add_smul]
  let oG : RingAct G O := { act := g, hom := hg, map_one := one, map_mul := mul, map_add := add }
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (g a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => _root_.GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs R hR D A G hG U O o a (g a) (g (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, oG, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, oG, fA, F]
end GlobalTheory.Mum
