import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PreUniformization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

open GlobalTheory.TorusModel

theorem exists_refine {S : Scheme.{0}} {H T₁ T₂ Z : Over S} [IsSeparated H.hom] [IsFinite T₁.hom] [IsFinite T₂.hom]
    {w₁ : T₁ ⟶ H} {w₂ : T₂ ⟶ H} {k₁ : Z ⟶ T₁} {k₂ : Z ⟶ T₂} (h : k₁ ≫ w₁ = k₂ ≫ w₂) :
    ∃ (T : Over S) (_ : IsFinite T.hom) (p₁ : T ⟶ T₁) (p₂ : T ⟶ T₂) (k : Z ⟶ T),
      p₁ ≫ w₁ = p₂ ≫ w₂ ∧ k ≫ p₁ = k₁ ∧ k ≫ p₂ = k₂ := by
  have : IsFinite (w₂.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsFinite w₂.left := IsFinite.of_comp w₂.left H.hom
  have hl : k₁.left ≫ w₁.left = k₂.left ≫ w₂.left := congrArg (·.left) h
  refine ⟨Over.mk (pullback.fst w₁.left w₂.left ≫ T₁.hom),
    inferInstanceAs (IsFinite (pullback.fst w₁.left w₂.left ≫ T₁.hom)), Over.homMk (pullback.fst _ _) rfl,
    Over.homMk (pullback.snd _ _) ?_, Over.homMk (pullback.lift k₁.left k₂.left hl) ?_,
    Over.OverMorphism.ext pullback.condition, Over.OverMorphism.ext (pullback.lift_fst _ _ _),
    Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  · change pullback.snd w₁.left w₂.left ≫ T₂.hom = pullback.fst w₁.left w₂.left ≫ T₁.hom
    rw [← Over.w w₂, ← Over.w w₁, pullback.condition_assoc]
  · change pullback.lift k₁.left k₂.left hl ≫ pullback.fst w₁.left w₂.left ≫ T₁.hom = Z.hom
    rw [pullback.lift_fst_assoc, Over.w]

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)

def Near {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) : Prop :=
  ∃ (T : Over (Sp R)) (_ : IsFinite T.hom) (k : Z ⟶ T) (w : T ⟶ Y.H) (w' : T ⟶ G),
    IsPointOf U (Y.Φ T w) w' ∧ k ≫ w = x ∧ k ≫ w' = x'

variable {U Y}

instance : IsSeparated Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).separated

instance : Smooth Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth

theorem pt_pull {T T' : Over (Sp R)} (k : T' ⟶ T) {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T' (k ≫ w)) (k ≫ w') := h.pull k (Y.rep.1 _ _ k w)

theorem pt_act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {T : Over (Sp R)}
    {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T (w ≫ Y.act.act c)) (w' ≫ a.act c) :=
  h.smul GlobalTheory.allSixLaws.1.globalFns hO c (Y.smul c T w)

theorem Near.comp {Z Z' : Over (Sp R)} {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') (r : Z' ⟶ Z) :
    Near U Y (r ≫ x) (r ≫ x') := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, r ≫ k, w, w', hw, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem Near.act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {Z : Over (Sp R)}
    {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') : Near U Y (x ≫ Y.act.act c) (x' ≫ a.act c) := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, k, _, _, pt_act hO c hw, (Category.assoc _ _ _).symm, (Category.assoc _ _ _).symm⟩

variable [IsNoetherianRing R] [hc : IsAdicComplete (maximalIdeal R) R]

theorem adic (T : Over (Sp R)) [IsFinite T.hom] : IsAdicColimit (maximalIdeal R) T :=
  FiniteTorsLift.isAdicColimit_of_isFinite_noetherian hc T

theorem pt_unique {T : Over (Sp R)} [IsFinite T.hom] {w : T ⟶ Y.H} {w' w'' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w')
    (h' : IsPointOf U (Y.Φ T w) w'') : w' = w'' := (existsUnique_point U (adic T) _).unique h h'

theorem Near.unique {Z : Over (Sp R)} {x : Z ⟶ Y.H} {x' x'' : Z ⟶ G} (h : Near U Y x x') (h' : Near U Y x x'') :
    x' = x'' := by
  obtain ⟨T, hT, k, w, w', hw, e, rfl⟩ := h
  obtain ⟨T₂, hT₂, k₂, w₂, w₂', hw₂, e₂, rfl⟩ := h'
  obtain ⟨T₃, _, p₁, p₂, l, h₁, rfl, rfl⟩ := exists_refine (e.trans e₂.symm)
  rw [Category.assoc, Category.assoc, pt_unique (pt_pull p₁ hw) (h₁ ▸ pt_pull p₂ hw₂)]

variable (U Y) in

def Loc {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) (e' : Frame U.LG.L x'.left)
    (e : Frame D.toPre.P.L (x ≫ Y.q).left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra R W) (_ : Module.Finite R W)
    (k : Z ⟶ Over.mk (spMap (algebraMap R W))) (w : Over.mk (spMap (algebraMap R W)) ⟶ Y.H)
    (w' : Over.mk (spMap (algebraMap R W)) ⟶ G) (g' : Frame U.LG.L w'.left) (g : Frame D.toPre.P.L (w ≫ Y.q).left)
    (ρ : Γ(Z.left, ⊤)ˣ), IsPointOf U (Y.Φ _ w) w' ∧ k ≫ w = x ∧ k ≫ w' = x' ∧ g'.IsGen ∧ g.IsGen ∧
    FrRel U w'.left (w ≫ Y.q).left g' g ∧
    (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good U.LG.L z J →
      val e' r z J = gm r z ⊤ ρ * val g' (r ≫ k.left) z J) ∧
    ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good D.toPre.P.L z J →
      val e r z J = gm r z ⊤ ρ * val g (r ≫ k.left) z J

open NumberField
open Formalism.MainNotions.DIV.Cons (SCF intO)

end GlobalTheory.RayEv.Transport
