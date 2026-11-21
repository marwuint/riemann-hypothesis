import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SectionsGroupRank

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VVCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_le_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k)
    (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

def pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) : LB.Sec (LB.LinComb L φ' ε) where
  f j := (Y'.presheaf.map (homOfLE (wchart_le_of_eq h e j)).op).hom ((h.app _).hom (s.f j))
  compat := by
    obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
    exact (H1.SectionArithmetic.pullSec s h).compat

theorem sval_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullTo s h e) r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact H1.SectionArithmetic.sval_pullSec s h r z hJ

end General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

omit [GrpObj A] in
theorem whisker_snd_left {T T' : Over S} (h : T' ⟶ T) :
    (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]

abbrev pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') :=
  pullSec (A := A) (L := L) (a := a) h s

abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J

theorem sv_pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A (pullS A a h s) r z J = sv A s (r ≫ (h ▷ A).left) z J :=
  sval_pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (h ▷ A).left
    (fun _ => whisker_snd_left A h) r z hJ

section Twist

variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sv_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A s' r z J = (val α r z J).val * sv A s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sv (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sv A s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sv A s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

theorem exists_isTwistPull (hL : L.IsLB) (hα : α.IsGen) (s : LB.Sec (LPow A L b T)) :
    ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', isTwistPull_of_sv A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩

end Twist

theorem exists_isActOf (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' :=
  exists_isTwistPull A hL θ.isGen s

variable (P : PolAV S) (N m : ℕ)

end GlobalTheory.VVCompare
