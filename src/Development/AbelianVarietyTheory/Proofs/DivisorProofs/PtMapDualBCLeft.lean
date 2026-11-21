import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

def lo : Localization.Away P'.f →+* O := IsLocalization.Away.lift P'.f hu

theorem lo_comp : (lo P' x0 hu).comp (algebraMap R _) = x0 := IsLocalization.Away.lift_comp _ _

@[nolint unusedArguments]
def OL (_P : GlobalTheory.HTMap.FP t ξ q) (_x : R →+* O) (_h : IsUnit (_x _P.f)) : Type := O

instance : CommRing (OL P' x0 hu) := inferInstanceAs (CommRing O)

instance : Algebra O (OL P' x0 hu) := inferInstanceAs (Algebra O O)

instance : Algebra (Localization.Away P'.f) (OL P' x0 hu) := (lo P' x0 hu).toAlgebra

instance : SMulCommClass (Localization.Away P'.f) O (OL P' x0 hu) :=
  ⟨fun a b c => @mul_left_comm O _ (lo P' x0 hu a) b c⟩

abbrev Bt : Type := OL P' x0 hu ⊗[Localization.Away P'.f] P'.B

def inB : P'.B →+* Bt P' x0 hu :=
  (Algebra.TensorProduct.includeRight : P'.B →ₐ[Localization.Away P'.f] Bt P' x0 hu).toRingHom

theorem inB_str : (inB P' x0 hu).comp P'.str = (algebraMap O (Bt P' x0 hu)).comp x0 := by
  refine RingHom.ext fun r => ?_
  change (Algebra.TensorProduct.includeRight : P'.B →ₐ[Localization.Away P'.f] Bt P' x0 hu)
    (algebraMap (Localization.Away P'.f) P'.B (algebraMap R _ r)) = algebraMap O (Bt P' x0 hu) (x0 r)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  exact RingHom.congr_fun (lo_comp P' x0 hu) r

abbrev Hs : Over (Sp O) := specO O (Bt P' x0 hu)

theorem sq : (spMap (inB P' x0 hu) ≫ P'.u.left) ≫ t.G.hom = spMap (algebraMap O (Bt P' x0 hu)) ≫ spMap x0 ≫ ξ := by
  rw [Category.assoc, GlobalTheory.HTMap.over_w P'.u, GlobalTheory.HTMap.spc_assoc, GlobalTheory.HTMap.spc_assoc, GlobalTheory.HTMap.spc_assoc]
  congr 1
  rw [← inB_str P' x0 hu]
  rfl

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

def aH (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Hs P' x0 hu ⟶ G' :=
  Over.homMk (hπ.lift _ _ (sq P' x0 hu)) (hπ.lift_snd _ _ _)

theorem aH_left_π (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    (aH P' x0 hu hπ).left ≫ π = spMap (inB P' x0 hu) ≫ P'.u.left := hπ.lift_fst _ _ _

def liftB {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D) (hβ : β.comp P'.str = (algebraMap O D).comp x0) :
    Bt P' x0 hu →ₐ[O] D :=
  letI : Algebra (Localization.Away P'.f) D := ((algebraMap O D).comp (lo P' x0 hu)).toAlgebra
  have e : β.comp (algebraMap (Localization.Away P'.f) P'.B) = algebraMap (Localization.Away P'.f) D :=
    IsLocalization.ringHom_ext (Submonoid.powers P'.f) (by
      rw [RingHom.comp_assoc]
      refine hβ.trans ?_
      change _ = (algebraMap O D).comp ((lo P' x0 hu).comp (algebraMap R _))
      rw [lo_comp])
  let f : OL P' x0 hu →ₐ[Localization.Away P'.f] D :=
    { (algebraMap O D : O →+* D) with commutes' := fun _ => rfl }
  let F : Bt P' x0 hu →ₐ[Localization.Away P'.f] D :=
    Algebra.TensorProduct.lift f { β with commutes' := fun r => RingHom.congr_fun e r } fun _ _ => Commute.all _ _
  { F.toRingHom with
    commutes' := fun c => by
      change F (algebraMap O (Bt P' x0 hu) c) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl }

theorem liftB_inB {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D)
    (hβ : β.comp P'.str = (algebraMap O D).comp x0) (z : P'.B) : liftB P' x0 hu β hβ (inB P' x0 hu z) = β z := by
  simp [liftB, inB]

def ptOf {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D) (hβ : β.comp P'.str = (algebraMap O D).comp x0) :
    specO O D ⟶ Hs P' x0 hu :=
  ptMap (liftB P' x0 hu β hβ)

theorem ptOf_aH_π {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D)
    (hβ : β.comp P'.str = (algebraMap O D).comp x0) (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    (ptOf P' x0 hu β hβ ≫ aH P' x0 hu hπ).left ≫ π = spMap β ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π, ← Category.assoc]
  change spMap (liftB P' x0 hu β hβ).toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]
  congr 2
  exact RingHom.ext fun z => liftB_inB P' x0 hu β hβ z

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

end GlobalTheory.FinPartAt
