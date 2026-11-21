import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RedTotal

section Units

variable {S : Type} [CommRing S] (J : Ideal S)

theorem appTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) :=
  congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem ΓSpecIso_injective (A : Type) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective

theorem fn_ext_levels [IsHausdorff J S] {a b : Γ(Spec (CommRingCat.of S), ⊤)}
    (h : ∀ e, (adicLevelι J (e + 1)).appTop.hom a = (adicLevelι J (e + 1)).appTop.hom b) : a = b := by
  apply ΓSpecIso_injective
  have := IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom b) fun n _ =>
      (appTop_specMap _ a).symm.trans ((congrArg _ (h n)).trans (appTop_specMap _ b))
  exact congrFun this ()

theorem exists_fn_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤))
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)) = ρ e) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤), ∀ e, (adicLevelι J (e + 1)).appTop.hom a = ρ e := by
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  let f : ∀ n : ℕ, Polynomial ℤ →+* S ⧸ J ^ (n + 1) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) ((Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n))
  have hf : ∀ n, f n Polynomial.X = (Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n) := fun n =>
    Polynomial.eval₂_X _ _
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, hf, hf, ← h m]
    exact (appTop_specMap _ _).symm
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    (IsAdicComplete.StrictMono.liftRingHom J ha f hc Polynomial.X), fun e => ΓSpecIso_injective _ ?_⟩
  rw [appTop_specMap, Iso.inv_hom_id_apply, ← hf]
  exact congrArg (fun q => q Polynomial.X) (IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha f hc (n := e))

theorem exists_unit_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)).val = (ρ e).val) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤)ˣ, ∀ e, pullU (adicLevelι J (e + 1)) ⊤ a = ρ e := by
  obtain ⟨a, ha⟩ := exists_fn_levels J (fun e => (ρ e).val) h
  obtain ⟨b, hb⟩ := exists_fn_levels J (fun e => ((ρ e)⁻¹).val) fun e => by
    have : Units.map (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom.toMonoidHom (ρ (e + 1)) = ρ e :=
      Units.ext (h e)
    rw [← this]; rfl
  have hab : a * b = 1 := fn_ext_levels J fun e => by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun e => Units.ext (ha e)⟩

end Units

section Gens

variable {S : Type} [CommRing S] (J : Ideal S) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_levels [IsHausdorff J S] (hL : L.IsLB) {φ : K → (Spec (CommRingCat.of S) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of S) ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z C, Good L z C → val u (adicLevelι J (e + 1)) z C = val u' (adicLevelι J (e + 1)) z C) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := Units.ext (fn_ext_levels J fun e =>
    (FormalPoint.appTop_eq_one_of_gm _ a fun z => by
      obtain ⟨C, hC⟩ := exists_good_pt hL z
      exact mul_eq_right.1 ((ha _ _ z C hC).symm.trans (hv e z C hC))).trans (map_one _).symm)
  exact corr_of_val hL fun y C hC => by rw [ha _ _ y C hC, h2, map_one, _root_.one_mul]

theorem exists_gen_levels [IsLocalRing S] [IsAdicComplete J S] (hL : L.IsLB)
    (φ : K → (Spec (CommRingCat.of S) ⟶ X)) (ε : K → ℤ) {Y : ℕ → Scheme.{0}} {ψ : ∀ e, K' → (Y e ⟶ X)}
    {ε' : K' → ℤ} (u : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε')) (hu : ∀ e, (u e).IsGen)
    (y : ∀ e : ℕ, Spec (CommRingCat.of (S ⧸ J ^ (e + 1))) ⟶ Y e)
    (h : ∀ e, FormEq (fun k => adicLevelι J (e + 1) ≫ φ k) ε (fun k => y e ≫ ψ e k) ε')
    (hc : ∀ e z C, Good L z C →
      val (u (e + 1)) (adicLevelMap J (Nat.le_succ (e + 1)) ≫ y (e + 1)) z C = val (u e) (y e) z C) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = val s (k ≫ adicLevelι J (e + 1)) z C := by
  obtain ⟨s₀, hs₀⟩ := DVR.exists_gen_of_local L hL φ ε
  choose ρ hρ using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm)
    (LB.pullGen L _ _ (u e) (y e)) (DVR.pullGen_isGen _ _ _ _ (hu e) _)
    (LB.pullGen L _ _ s₀ (adicLevelι J (e + 1))) (DVR.pullGen_isGen _ _ _ _ hs₀ _)
  have hρ' : ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = gm k z ⊤ (ρ e) * val s₀ (k ≫ adicLevelι J (e + 1)) z C := fun e Z k z C hC =>
    (val_pull hC _ _ _).symm.trans ((hρ e Z k z C hC).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _)))
  obtain ⟨a, ha⟩ := exists_unit_levels J ρ fun e => by
    refine (FormalPoint.appTop_eq_of_gm _ (𝟙 _) (ρ (e + 1)) (ρ e) fun z => ?_).trans (by simp)
    obtain ⟨C, hC⟩ := exists_good_pt hL z
    have e₁ := hρ' (e + 1) _ (adicLevelMap J (Nat.le_succ (e + 1))) z C hC
    have e₂ := hρ' e _ (𝟙 _) z C hC
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [hc e z C hC, adicLevelMap_ι, e₂] at e₁
    exact (mul_right_cancel e₁).symm
  refine ⟨scaleGen a s₀, scaleGen_isGen a hs₀, fun e Z k z C hC => ?_⟩
  rw [val_scaleGen a s₀ _ hC, hρ' e Z k z C hC, ← ha e]
  exact congrArg (· * _) (gm_pull k _ z ⊤ trivial a)

end Gens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}

theorem formEq_mult {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ'))
        (fun k => (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim DegPre.gtε thε)
      (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ')) (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ f
  have p : ∀ α, ∏ k, f (DegPre.gtφT D T b α k) ^ DegPre.gtε k =
      (f (DVR.cP D T α * b).left)⁻¹ * f (DVR.cP D T α).left * f b.left * (f (1 : T ⟶ D.P.A).left)⁻¹ := fun α => by
    have := FormalPoint.prod_gtφT (𝟙 T) b α f
    simpa only [Over.id_left, Category.id_comp] using this
  have q := prod_cub (DVR.cP D T χ) (DVR.cP D T χ') b f
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [p, p, p]
  refine (congrArg (_ * ·) q).trans ?_
  rw [DVR.cPoint_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : PreU I D A G) {S : Type} [CommRing S] {φ : R →+* S}

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
open FormalPoint in

theorem reduction_succ (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ reduction I x (e + 1) = reduction I x e ≫ thickMap R I e G := by
  have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, h₄, reduction_fstG, reduction_fstG]
  exact adicLevelMap_ι_assoc _ _ _

variable [IsLocalRing S]

end Main

end GlobalTheory.RedTotal
