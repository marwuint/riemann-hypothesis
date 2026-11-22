import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.OpenModelSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCoeffFieldOfCoeff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RangeJSubsetAbLocus

noncomputable section

namespace GlobalTheory.ModelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModuliCompare GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Obj

variable {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {f : S' ⟶ S}

def objOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : Obj D l b (f ≫ s) :=
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    eta := fun a => secPull m.cart (o.eta a)
    eta_add := fun a c => by rw [o.eta_add, map_mul]
    eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
    etaA := fun a => secPull m.cart (o.etaA a)
    etaA_add := fun a c => by rw [o.etaA_add, map_mul]
    etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
    geom := fun k _ _ x β hx => by
      obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
      refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
        hI, fun a => ?_, fun a ha => ?_⟩
      · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
          GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
        exact hdet τ
      · apply Over.OverMorphism.ext
        show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
        rw [Category.assoc, m.act, Category.assoc]
      · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
          m.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha)) }

def objMapOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : ObjMap (objOfSABMap o m) o f :=
  ⟨m, fun _ => secPull_left m.cart _, fun _ => secPull_left m.cart _⟩

theorem sec_eq_secPull {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) {e : 𝟙_ (Over S) ⟶ t.G}
    {e' : 𝟙_ (Over S') ⟶ t'.G} (h : e'.left ≫ m.φ = f ≫ e.left) : e' = secPull m.cart e := by
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · exact h.trans (secPull_left m.cart _).symm
  · rw [Over.w, Over.w]

end Obj

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev Model₂ (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) : Type 1 :=
  IndefiniteRowSideFullHecke.OpenModelSections.Model (X₀ := Xo.X) (str := Xo.s) Xo.univ (isCoeffField_of_coeff c) β

def toSecond (Y : Model Xo c β) : Model₂ Xo c β where
  X := Y.X
  s := Y.s
  normal := Y.normal
  proj := Y.proj
  flat := Y.flat
  j := Y.jQ
  j_over := Y.jQ_over
  j_open := Y.jQ_open
  j_dense := Y.jQ_dense
  t := Y.t
  t₀ := Y.oF.t
  toUniv := Y.m0.toSABMap
  toModel := Y.m
  ab y := Set.ext_iff.1 Y.ab_gen y

variable (Y : Model Xo c β)

def secEquiv : (𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) ≃
    (Over.mk (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseChangeFst Xo.s (isCoeffField_of_coeff c)) ⟶ Xo.univ.t.G) where
  toFun σ := Over.homMk (σ.left ≫ Y.m0.toSABMap.φ) (by
    have h : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    exact (Category.assoc _ _ _).trans ((congrArg (σ.left ≫ ·) Y.m0.cart.1.w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.id_comp _)))))
  invFun σ := Over.homMk ((toSecond Y).liftSec σ) (Y.m0.cart.1.lift_snd _ _ _)
  left_inv σ := Over.OverMorphism.ext (Y.m0.cart.1.hom_ext (Y.m0.cart.1.lift_fst _ _ _)
    ((Y.m0.cart.1.lift_snd _ _ _).trans (Over.w σ).symm))
  right_inv σ := Over.OverMorphism.ext (Y.m0.cart.1.lift_fst _ _ _)

theorem secEquiv_left (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    (secEquiv Y σ).left = σ.left ≫ Y.m0.toSABMap.φ := rfl

end Model

end GlobalTheory.ModelCompare
