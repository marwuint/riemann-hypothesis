import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']

structure Cmp (φ : R →+* V) (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) where

  pb : IsGrpPullback G' G (spMap φ) F

  wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)

  wL_map : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL

  β : D'.P.A.left ⟶ D.P.A.left

  pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) β

  v : LB.Iso D'.P.L (D.P.L.pull β)

  v_gen : v.IsGen

  xe : D'.X ≃+ D.X

  c_pr : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left

  lev : ∀ (e : ℕ) (Z : Scheme.{0}) (x' : Z ⟶ (thickObj V I' e G').left) (x : Z ⟶ (thickObj R I e G).left),
    x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F →
    x' ≫ (U'.gt e).pG.left ≫ β = x ≫ (U.gt e).pG.left ∧
    ∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
      (∀ χ : D'.X, val ((U.gt e).t (xe χ)) x z J = val ((U'.gt e).t χ) x' z J' *
        ∏ k : Fin 4, gw v (x' ≫ D'.Oφ (U'.gt e).pG χ k) z (J (x' ≫ D'.Oφ (U'.gt e).pG χ k ≫ β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG χ k)) ^ Oinvε k) ∧
      ∀ (k : U.P.L.L.ι) (k' : U'.P.L.L.ι), (fstG I e G).left (x z) ∈ U.P.L.L.U k → (fstG I' e G').left (x' z) ∈ U'.P.L.L.U k' →
        gw v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) *
            gw (U'.w e) x' z (J' (x' ≫ (U'.gt e).pG.left)) (fun _ => k') =
          gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => k) * gw wL (x' ≫ (fstG I' e G').left) z k k'

  map_le : I.map φ ≤ I' := by first | assumption | exact (Ideal.map_id _).le

def Under {D₀ : DegData R I} (U : PreU I D₀.toPre A G) (U₀ : UnifPre I D₀ A G) : Prop :=
  U.gen = U₀.gen ∧ U.P.L = U₀.LG ∧ HEq U.P.c U₀.cubG ∧ HEq U.P.sym U₀.symG ∧ U.gt = U₀.gt ∧ HEq U.w U₀.w

abbrev withPsi (D : DegPre R) (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
    (h : ∀ χ, (psi χ).IsGen) : DegPre R := setPsi D psi h

namespace Cmp

omit [IsDomain R] in

theorem spMap_ringHom_id : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

theorem grpPullback_id {S : Scheme.{0}} (H : Over S) [GrpObj H] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback H H f (𝟙 H.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have hq : (𝟙 H : H ⟶ H).left ≫ H.hom = H.hom ≫ 𝟙 S := by simp
  have e₁ : x₀ = toBase hq x := Over.OverMorphism.ext hx
  have e₂ : y₀ = toBase hq y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← toBase_mul_of_isMonHom (𝟙 H) hq]
  rfl

theorem cpMap_id {S : Scheme.{0}} {H : Over S} [GrpObj H] [IsCommMonObj H] (P : CP H) {f : S ⟶ S} (hf : f = 𝟙 S)
    (hw : 𝟙 H.left ≫ H.hom = H.hom ≫ f) : IsCPMap P P f (𝟙 H.left) hw (idIso P.L.L) := by
  subst hf
  exact IsCPMap.id P

theorem mono_fstG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have hs : Function.Surjective (Ideal.Quotient.mk (I ^ (e + 1))) := Ideal.Quotient.mk_surjective
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) := ConcreteCategory.epi_of_surjective _ hs
  have : Mono (thick R I e) := Scheme.Spec.map_mono (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))).op
  exact (inferInstance : Mono (pullback.fst G.hom (thick R I e)))

def refl (U : PreU I D A G) : Cmp (RingHom.id R) U U (𝟙 G.left) where
  pb := grpPullback_id G spMap_ringHom_id
  wL := idIso U.P.L.L
  wL_map := cpMap_id U.P spMap_ringHom_id _
  β := 𝟙 _
  pbB := grpPullback_id D.P.A spMap_ringHom_id
  v := idIso D.P.L
  v_gen := idIso_isGen D.P.isLB
  xe := AddEquiv.refl _
  c_pr x := by rw [spMap_ringHom_id]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lev e Z x' x hx := by
    have := mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨by rw [Category.comp_id], fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (val_change ((U.gt e).t_gen χ) x hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_
      rw [Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
    · rw [gw_idIso _ _ _ (hJ _) (hJ' _), gw_idIso U.P.L.L (x ≫ (fstG I e G).left) z hk hk']
      have h := (isGen_iff (U.w e)).1 (U.w_gen e) Z x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (U.gt e).pG.left))
        (fun _ => k) (fun _ => k') (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U.gt e).pG.left))
        (mem_pull.2 hk) (mem_pull.2 hk')
      have g := gm_pull_g U.P.L.L (fstG I e G).left x z (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
      rw [h, g]
      exact (congrArg (· * _) (inv_mul_cancel_right _ _).symm).trans (mul_right_comm _ _ _)

variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}

end Cmp

end GlobalTheory.LN
end
