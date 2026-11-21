import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtOmPHtEval
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.KernelNoTorsion

namespace GlobalTheory.MuConst

variable (S : Scheme.{0}) (N : ℕ)

def torsPts (T : Over S) : Subgroup (T ⟶ Gm S) := (powMonoidHom N).ker

theorem mem_torsPts {T : Over S} (x : T ⟶ Gm S) : x ∈ torsPts S N T ↔ x ^ N = 1 := Iff.rfl

def torsFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (torsPts S N T.unop)
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        rw [mem_torsPts, ← MonObj.comp_pow, (mem_torsPts S N x.1).1 x.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp f g := by ext x; exact Category.assoc _ _ _

def torsRep : (torsFunctor S N ⋙ forget _).RepresentableBy (torsion (Gm S) N) where
  homEquiv {T} :=
    { toFun := fun x => (⟨x ≫ torsion.ι (Gm S) N, by
        rw [mem_torsPts, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩ : torsPts S N T)
      invFun := fun y => torsionLift (y : torsPts S N T).1 (y : torsPts S N T).2
      left_inv := fun x => torsion_hom_ext (torsionLift_ι _ _)
      right_inv := fun y => Subtype.ext (torsionLift_ι _ _) }
  homEquiv_comp f x := Subtype.ext (Category.assoc _ _ _)

instance grpTors : GrpObj (torsion (Gm S) N) := GrpObj.ofRepresentableBy _ _ (torsRep S N)

theorem mul_ι {T : Over S} (x y : T ⟶ torsion (Gm S) N) :
    (x * y) ≫ torsion.ι (Gm S) N = (x ≫ torsion.ι (Gm S) N) * (y ≫ torsion.ι (Gm S) N) :=
  congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy _ _ (torsRep S N)).hom.app (op T)).hom.map_mul x y)

instance isCommMonObj_tors : IsCommMonObj (torsion (Gm S) N) := by
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  apply torsion_hom_ext
  rw [mul_ι, mul_ι, mul_comm]

variable [NeZero N]

abbrev cstRing : CommRingCat.{0} := CommRingCat.of (GlobalTheory.CartierDual ZU (AddMonoidAlgebra ZU (ZMod N)))

abbrev cstAff : Over (Spec ZU) := (Spec (cstRing N)).asOver (Spec ZU)

def cst : Over S := (Over.pullback (toZ S)).obj (cstAff N)

instance grpCst : GrpObj (cst S N) := Functor.grpObjObj

instance isCommMonObj_cst : IsCommMonObj (cst S N) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (cstAff N)))

abbrev muCst : Over S := torsion (Gm S) N ⊗ cst S N

def incl : torsion (Gm S) N ⟶ muCst S N := lift (𝟙 _) (toUnit _ ≫ η[cst S N])

section Props

open GlobalTheory.HTSheaf

variable (N : ℕ)

theorem one_ι {T : Over S} : (1 : T ⟶ torsion (Gm S) N) ≫ torsion.ι (Gm S) N = 1 :=
  congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy _ _ (torsRep S N)).hom.app (op T)).hom.map_one)

instance isMonHom_ι : IsMonHom (torsion.ι (Gm S) N) where
  one_hom := by
    have h := one_ι S N (T := 𝟙_ (Over S))
    rwa [Hom.one_def, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h
  mul_hom := by
    have h := mul_ι S N (fst (torsion (Gm S) N) (torsion (Gm S) N)) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1

variable [NeZero N]

instance isMonHom_incl : IsMonHom (incl S N) := by
  unfold incl
  infer_instance

end Props

end GlobalTheory.MuConst
