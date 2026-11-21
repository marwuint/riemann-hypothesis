import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]

theorem TQ.comp_i_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) : (t ≫ Q.i) ≫ Q.q = 1 := by
  rw [Category.assoc, Q.isKernel.w, ← Category.assoc]
  simp only [toUnit_unique (t ≫ toUnit _) (toUnit T)]
  rfl

theorem TQ.Desc.cubV_torus {Q : TQ G X} {P : CP G} (D : Q.Desc P) {T : Over S} {z : T.left} {J}
    (hJ : Good D.M.L.L z J) (h : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S) (x : T ⟶ splitTorus S X) (y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV D.M.c (T := Over.mk (T.hom ≫ 𝟙 S)) z J
      (toBase h (x ≫ Q.i)) (toBase h y) (toBase h u)) = 1 := by
  have e : toBase h (x ≫ Q.i) = 1 := by
    ext
    have h1 := congrArg (fun f => f.left) (TQ.comp_i_q Q x)
    simp only [Over.comp_left] at h1
    rw [one_left] at h1 ⊢
    simp [toBase, h1]
  rw [e]
  exact (isCub_cubV D.M.c hJ).face _ _

private theorem comp_one_uniformization {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (x : T ⟶ T') :
    x ≫ (1 : T' ⟶ G) = 1 := by
  show x ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _)]

private theorem one_comp_of_isMonHom' {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) [IsMonHom q]
    {T : Over S} : (1 : T ⟶ G) ≫ q = 1 := by
  show (toUnit _ ≫ η) ≫ q = toUnit _ ≫ η
  rw [Category.assoc, IsMonHom.one_hom]

private theorem prod_mul_inv_four_eq_of_mul_eq {U : Type} [CommGroup U] {C w a b c d e f g : U}
    (hv : e * f * g * w = a * b * c * d * C) :
    w * a⁻¹ * (w * b⁻¹) * (w * c⁻¹) * (w * d⁻¹) = C * (w * e⁻¹) * (w * f⁻¹) * (w * g⁻¹) := by
  have hC : C = (a * b * c * d)⁻¹ * (e * f * g * w) := by rw [hv]; group
  rw [hC]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem oneGen_isGen_uniformization {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  unfold LB.Gen.IsGen
  simp [LB.oneGen]
  intro i j
  unfold LB.LinComb
  simp

private theorem mul_inv_eq_mul_mul_mul_inv {U : Type} [CommGroup U] (w m s : U) : w * m⁻¹ = s * (w * (m * s)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem eq_mul_inv_of_one_eq_mul_inv_mul {U : Type} [CommGroup U] {a b v : U} (h : 1 = a * b⁻¹ * v) : v = b * a⁻¹ := by
  calc v = (a * b⁻¹)⁻¹ * (a * b⁻¹ * v) := by group
    _ = b * a⁻¹ := by rw [← h]; group

theorem TQ.Desc.exists_even {Q : TQ G X} {P : CP G} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hi := Q.i_hom
  have hq := Q.q_hom
  have hw : PGen D.w := (isGen_iff D.w).1 D.map.gen
  have hF : FormEq (K := PEmpty) (K' := Fin 2) PEmpty.elim PEmpty.elim
      ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] ![1, -1] := by
    intro U _ h
    simp [Fin.prod_univ_two]
  obtain ⟨t, ht, htv⟩ := exists_gen D.M.L.isLB hF (LB.oneGen D.M.L.L) (oneGen_isGen_uniformization _)
  have hc : ∀ k, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] : Fin 2 → _) k ≫ Q.q.left =
      𝟙 _ ≫ (![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] : Fin 2 → _) k := by
    intro k
    fin_cases k
    · show Q.i.left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left]
      simpa using congrArg (fun f => f.left) (TQ.comp_i_q Q (𝟙 _))
    · show (1 : splitTorus S X ⟶ G).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, one_comp_of_isMonHom']
  obtain ⟨a, ha, hpm⟩ := CubTransport.exists_pmaps hw D.M.L.isLB P.L.isLB (𝟙 _) hc t ht
  have key : ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J : (T.left ⟶ Q.B.left) → D.M.L.L.ι)
      (J' : (T.left ⟶ G.left) → P.L.L.ι), Good D.M.L.L z J → Good P.L.L z J' →
      val a x.left z J' = gw D.w (1 : T ⟶ G).left z (J ((1 : T ⟶ G).left ≫ Q.q.left)) (J' (1 : T ⟶ G).left) *
        (gw D.w (x ≫ Q.i).left z (J ((x ≫ Q.i).left ≫ Q.q.left)) (J' (x ≫ Q.i).left))⁻¹ := by
    intro T x z J J' hJ hJ'
    have e1 := CubTransport.val_pmaps hc hpm x.left hJ hJ'
    rw [htv _ _ _ _ hJ, val_one, Fin.prod_univ_two] at e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, ← Over.comp_left,
      comp_one_uniformization] at e1
    exact eq_mul_inv_of_one_eq_mul_inv_mul e1
  refine ⟨⟨a, ha, ?_⟩, ?_⟩
  · intro T x y u z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (x ≫ Q.i) (y ≫ Q.i) (u ≫ Q.i)
    rw [TQ.Desc.cubV_torus D hJ _ x (y ≫ Q.i) (u ≫ Q.i), _root_.one_mul] at hv
    simp only [← MonObj.mul_comp] at hv
    have key' := fun v : T ⟶ splitTorus S X => key T v z J J' hJ hJ'
    simp only [key']
    exact prod_mul_inv_four_eq_of_mul_eq hv
  · intro T x z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hs := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.1 (x ≫ Q.i)
    have e3 : (x ≫ Q.i).left ≫ Q.q.left = (1 : T ⟶ Q.B).left := by
      rw [← Over.comp_left, TQ.comp_i_q]
    have hsym : val D.M.sym ((x ≫ Q.i).left ≫ Q.q.left) z J = 1 := by
      rw [e3]; exact CP.val_sym_one _ hJ
    rw [hsym, _root_.one_mul, ← GrpObj.inv_comp] at hs
    rw [key T x⁻¹ z J J' hJ hJ', key T x z J J' hJ hJ', hs]
    exact mul_inv_eq_mul_mul_mul_inv _ _ _

end GlobalTheory.UU
end
