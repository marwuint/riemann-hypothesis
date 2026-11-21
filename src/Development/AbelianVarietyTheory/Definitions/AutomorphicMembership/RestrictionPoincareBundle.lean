import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap thickTrans)
open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf (hMap sE)
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor GlobalTheory.Vert GlobalTheory.FormalPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

section Classes

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def IsRigCls (c : SmallPic G.left) : Prop := smallPull (eSec G) c = 0

def RigPic : Type := {c : SmallPic G.left // IsRigCls G c}

variable {G}

def diagCls (w : G ⟶ G) (P : RigPic (G ⊗ G)) : SmallPic G.left := smallPull (lift (𝟙 G) w).left P.1

variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace tens

variable {X X' : Scheme.{0}} (t : SAB H X) (Λ : Unim E)

def diag (P : RigPic ((tens t Λ).G ⊗ (tens t Λ).G)) : SmallPic (tens t Λ).G.left := diagCls ((tens t Λ).act.act H.w0) P

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

end tens

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) (Λ : Unim E)

def abPartAct : OAct (𝓞 E) U.D.toPre.P.A := letI := H.starRing; ofRingAct U.oD.onB.toRingAct

abbrev abTens : Over (Sp R) := Λ.obj (abPartAct U)

theorem isLinearHom_q (e : ℕ) : IsLinearHom (t.act.pullback (thick R I e) _) ((abPartAct U).pullback (thick R I e) _)
    (U.U.gt e).q :=
  letI := H.starRing
  ⟨(U.U.gt e).q_hom, fun c => U.lin.q_lin e c⟩

def qTens (e : ℕ) : thickObj R I e (tens t Λ).G ⟶ thickObj R I e (abTens U Λ) :=
  ((tens.isTensor t Λ).pullback (thick R I e)).mapRight ((Λ.isTensor (abPartAct U)).pullback (thick R I e))
    (isLinearHom_q U e)

theorem isLinearHom_qTens (e : ℕ) : IsLinearHom ((tens t Λ).act.pullback (thick R I e) _)
    ((Λ.act (abPartAct U)).pullback (thick R I e) _) (qTens U Λ e) := IsTensor.isLinearHom_mapRight _ _ _

end Unif

section Point

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (Λ : Unim E)

def defIdeal : Ideal ↥(intO ↥C.S) := (maximalIdeal A.R).map A.f

abbrev gPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (tens A.t Λ).G

abbrev bPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (abTens A.U Λ)

abbrev gtLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (gPt A Λ)

abbrev bLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (bPt A Λ)

def levToDat (G : Over (Sp A.R)) (e : ℕ) : (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)).left ⟶
    (thickObj A.R (maximalIdeal A.R) e G).left := hMap (φ := A.f) (hφ := le_rfl) G _ (𝟙 _)

theorem isGrpPullback_levToDat (G : Over (Sp A.R)) [GrpObj G] (e : ℕ) :
    IsGrpPullback (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)) (thickObj A.R (maximalIdeal A.R) e G)
      (sE A.f le_rfl e) (levToDat A G e) :=
  @Out.PullGtPf.isGrpPullback_hMap _ _ _ _ _ _ _ _ A.f le_rfl e G _ _ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _)))

def prLev (e : ℕ) : gtLev A Λ e ⟶ bLev A Λ e :=
  Over.homMk ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift (levToDat A _ e ≫ (qTens A.U Λ e).left) (gtLev A Λ e).hom
    (by rw [Category.assoc, Over.w]; exact (isGrpPullback_levToDat A _ e).1.w))
    ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_snd _ _ _)

@[reassoc] theorem prLev_levToDat (e : ℕ) :
    (prLev A Λ e).left ≫ levToDat A _ e = levToDat A _ e ≫ (qTens A.U Λ e).left :=
  (isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_fst _ _ _

instance isMonHom_prLev (e : ℕ) : IsMonHom (prLev A Λ e) :=
  have := (isLinearHom_qTens A.U Λ e).1
  Out.PullGtPf.isMonHom_of_grpPullback (isGrpPullback_levToDat A _ e) (isGrpPullback_levToDat A _ e) (qTens A.U Λ e) _
    (prLev_levToDat A Λ e)

variable {X : Scheme.{0}} {π : X ⟶ Y.X} {t : SAB H X} (m : SABMap t Y.t π) (z : Sp ↥(intO ↥C.S) ⟶ X) (hz : z ≫ π = P.yt)

end Point

end GlobalTheory.LocM
