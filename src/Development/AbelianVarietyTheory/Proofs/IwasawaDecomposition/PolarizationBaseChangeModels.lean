import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFin

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {π : X' ⟶ X} {F : G'.left ⟶ G.left} {S S' : Type} [CommRing S] [CommRing S']

def tanPush (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' →ₗ[S] TanM (x ≫ π) G where
  toFun v := mkT (pushHom h (overAt x (DualNumber S)) (tv v)) (by
    have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) (tv v)) =
        pushHom h (overAt x (DualNumber S)) (smT x 0 (tv v)) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, tv_mem]
    exact map_one _)
  map_add' u v := tanM_ext (map_mul (pushHom h (overAt x (DualNumber S))) _ _)
  map_smul' a v := tanM_ext (Over.OverMorphism.ext (Category.assoc _ _ _))

theorem tanPush_bijective (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : Function.Bijective (tanPush h x) := by
  have inj : Function.Injective (pushHom h (overAt x (DualNumber S))) := fun p q hpq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))
  refine ⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩
  let p : overAt x (DualNumber S) ⟶ G' :=
    Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)
  have hp : pushHom h (overAt x (DualNumber S)) p = tv V := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  refine ⟨mkT p (inj ?_), tanM_ext hp⟩
  have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) =
      pushHom h (overAt x (DualNumber S)) (smT x 0 p) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [← e, hp, map_one]
  exact tv_mem V

def tanEquiv (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' ≃ₗ[S] TanM (x ≫ π) G :=
  LinearEquiv.ofBijective _ (tanPush_bijective h x)

theorem tanPull_tanEquiv (h : IsGrpPullback G' G π F) (φ : S →+* S') {x : Sp S ⟶ X'} {x' : Sp S' ⟶ X'}
    (e : spMap φ ≫ x = x') (e' : spMap φ ≫ x ≫ π = x' ≫ π) (v : TanM x G') :
    tanPull φ e' (tanEquiv h x v) = tanEquiv h x' (tanPull φ e v) :=
  tan_ext_left (Category.assoc _ _ _).symm

end Push

theorem ev_pull_g {X X' : Scheme.{0}} {S : Type} [CommRing S] (L : LB X) (π : X' ⟶ X) (z : Sp S ⟶ X')
    (J J' : PUnit → L.ι) (h : ⊤ ≤ z ⁻¹ᵁ ((L.pull π).U J ⊓ (L.pull π).U J'))
    (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))) :
    ev z _ h ((L.pull π).g J J').val = ev (z ≫ π) _ h' (L.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))
  have e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e, ← ev_appLE z π le h]
  rfl

end GlobalTheory.PolFin
