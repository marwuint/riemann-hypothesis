import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BeTransSymmOfWitData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsWitDataLevelAgree
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed

noncomputable section

namespace GlobalTheory.LevelRigid

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem pairing_weilMove (hW : Out.WeilSt) {S S' X : Scheme.{0}} [IsLocallyNoetherian S'] (hX : Subsingleton X)
    {G : Over S} [GrpObj G] {L₀ : LB G.left} (hL₀ : L₀.IsLB) (P₁ : Out.PolAV S') {f : S' ⟶ S}
    {φ : P₁.A.left ⟶ G.left} (hp : IsGrpPullback P₁.A G f φ) (w : LB.Iso P₁.L (L₀.pull φ)) (hw : w.IsGen)
    {tS : X ⟶ S'} {t₀ : X ⟶ S} (ht : t₀ = tS ≫ f) (n : ℕ) (x y : Over.mk tS ⟶ P₁.A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (x₀ y₀ : Over.mk t₀ ⟶ G) (hx₀ : x₀.left = x.left ≫ φ) (hy₀ : y₀.left = y.left ≫ φ)
    (c : Γ(X, ⊤)ˣ) (hG : Out.WeilIs G L₀ n x₀ y₀ c) : Out.WeilIs P₁.A P₁.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW S' P₁ n (Over.mk tS)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hX q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (Out.overRes (T := Over.mk t₀) V).hom = (Out.overRes (T := Over.mk tS) V).hom ≫ f := by
    rw [Category.id_comp]
    show V.ι ≫ t₀ = (V.ι ≫ tS) ≫ f
    rw [ht, Category.assoc]
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hx₀]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hy₀]; rfl
  obtain ⟨θx, hθx, mx⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θy₀ mvy
  have hm := H1.commIsOf_move (T := Out.overRes (T := Over.mk tS) V) (T₀ := Out.overRes (T := Over.mk t₀) V) hp
    (𝟙 _) hτ hL₀ P₁.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my
    (Out.unitRes (T := Over.mk t₀) V c) (Out.unitRes (T := Over.mk tS) V c)
    (fun Z r z => by rw [Category.comp_id]; rfl) (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := H1.commIsOf_unique P₁.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem pairing_nondeg (hW : Out.WeilSt) (hND : Out.WeilNondegSt) (hBC : Out.PolBaseChangeSt)
    {S : Scheme.{0}} (B : Out.PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ) (hn : (n : F) ≠ 0) (u : Over.mk t ⟶ B.A)
    (hu : u ^ n = 1) (h : ∀ z : Over.mk t ⟶ B.A, z ^ n = 1 → Out.WeilIs B.A B.L n u z 1) : u = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hBC S (Spec (CommRingCat.of F)) t B
  obtain ⟨w, hw⟩ := LBIso.symm ⟨tw, htw⟩
  have hp : IsGrpPullback P'.A B.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  let i : Over.mk ((Out.baseOver (Spec (CommRingCat.of F))).hom ≫ t) ⟶ Over.mk t :=
    Over.homMk (𝟙 _) (by simp)
  have hi : ∀ a b : Over.mk t ⟶ B.A, i ≫ a = i ≫ b → a = b := fun a b hab => by
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left hab
    simpa [i] using this
  have tb1 : Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A) = 1 := by
    have e := hmul (Out.baseOver _) 1 1
    rw [_root_.one_mul] at e
    exact mul_left_cancel (a := Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A)) (by rw [_root_.mul_one]; exact e.symm)
  have tbpow : ∀ (z : Out.baseOver _ ⟶ P'.A) (m : ℕ), Out.toBase hg.w (z ^ m) = Out.toBase hg.w z ^ m := by
    intro z m
    induction m with
    | zero => rw [pow_zero, pow_zero, tb1]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  let push : (Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) → (Over.mk t ⟶ B.A) := fun z =>
    Over.homMk (z.left ≫ g) (by
      show (z.left ≫ g) ≫ B.A.hom = t
      rw [Category.assoc, hg.w, ← Category.assoc, Over.w z]; simp)
  have tbpush : ∀ z, Out.toBase hg.w z = i ≫ push z := fun z =>
    Over.OverMorphism.ext (by simp [i, push, Out.toBase])
  have pinj : ∀ a b : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, a.left ≫ g = b.left ≫ g → a = b :=
    fun a b hab => Over.OverMorphism.ext (hg.hom_ext hab (by rw [Over.w a, Over.w b]))
  let u' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift u.left (𝟙 _) (by rw [Over.w u]; simp)) (hg.lift_snd _ _ _)
  have hu'g : u'.left ≫ g = u.left := hg.lift_fst _ _ _
  have hpu : push u' = u := Over.OverMorphism.ext hu'g
  have hu' : u' ^ n = 1 := by
    apply pinj
    have e : Out.toBase hg.w (u' ^ n) = Out.toBase hg.w 1 := by
      rw [tbpow, tb1, tbpush, hpu, ← MonObj.comp_pow, hu, MonObj.comp_one]
    exact congrArg CommaMorphism.left e
  have hall : ∀ y' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, y' ^ n = 1 →
      Out.WeilIs P'.A P'.L n u' y' 1 := by
    intro y' hy'
    have hy : push y' ^ n = 1 := by
      apply hi
      rw [MonObj.comp_pow, ← tbpush, ← tbpow, hy', tb1, MonObj.comp_one]
    exact pairing_weilMove hW inferInstance B.isLB P' hp w hw (tS := 𝟙 _) (t₀ := t) (Category.id_comp t).symm n
      u' y' hu' hy' u (push y') hu'g.symm rfl 1 (h _ hy)
  have h1 := hND F P' n hn u' hu' hall
  apply hi
  rw [← hpu, ← tbpush, h1, tb1, MonObj.comp_one]

theorem pairing_tors {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {T : Over S} (z : T ⟶ G)
    (f : G ⟶ G') (hf : IsMonHom f) (n : ℕ) (hz : z ^ n = 1) : (z ≫ f) ^ n = 1 := by
  have := hf
  rw [← MonObj.pow_comp, hz, MonObj.one_comp]

end
end GlobalTheory.LevelRigid
