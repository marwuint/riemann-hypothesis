import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem val₂_one (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good Lr.L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ h₀ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull₂ (f g : A ⟶ A) (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good Lr.L z J) (a b : T ⟶ A) :
    val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g f' g' : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    (w : LB.Gen (LB.LinComb Lr.L (rosatiφ A (f * f') (g * g')) rosatiε)) (hw : w.IsGen)
    (w₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ w z J x y * cubV c z J x (y ≫ g) (y ≫ g') =
      cubV c z J (x ≫ f) (x ≫ f') y * (val₂ u z J x y * val₂ u' z J x y) := by
  let p : A ⊗ A ⟶ A := fst A A
  let q : A ⊗ A ⟶ A := snd A A
  let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
  have e₀ : e ≫ p = 1 := lift_fst _ _
  have e₁ : e ≫ q = 1 := lift_snd _ _
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good Lr.L z J →
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ w (lift p q).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift p (lift (q ≫ g) (q ≫ g'))).left)) σ.left z J =
        val₂ w z J (σ ≫ p) (σ ≫ q) * cubV c z J (σ ≫ p) (σ ≫ q ≫ g) (σ ≫ q ≫ g') ∧
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (p ≫ f) (lift (p ≫ f') q)).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift p q).left) (LB.pullGen Lr.L _ _ u' (lift p q).left)))
        σ.left z J = cubV c z J (σ ≫ p ≫ f) (σ ≫ p ≫ f') (σ ≫ q) *
          (val₂ u z J (σ ≫ p) (σ ≫ q) * val₂ u' z J (σ ≫ p) (σ ≫ q)) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ w σ hJ _ _) (val_cub c σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ _ _ u σ hJ _ _) (val_pull₂ _ _ u' σ hJ _ _))))⟩
  have key := (ev (lift x y) hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => by
      refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub (p ≫ f) (p ≫ f') q k)
        (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g p q k) (prod_ros f' g' p q k))).trans
        (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros (f * f') (g * g') p q k)
          (prod_cub p (q ≫ g) (q ≫ g') k)).symm)
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc p]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ c.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu _) (pullGen_isGen _ _ _ _ hu' _))) (fun y I hI => by
      have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, val₂_one _ _ w w₀ hI, val₂_one _ _ u h₀ hI, val₂_one _ _ u' h₀' hI, C.face, C.face₃]
      simp) _ (lift x y).left z J hJ) (ev (lift x y) hJ).2)
  have r₀ : lift x y ≫ p = x := lift_fst _ _
  have r₁ : lift x y ≫ q = y := lift_snd _ _
  simp only [← Category.assoc, r₀, r₁] at key
  exact key

end GlobalTheory.TauBalAdd
