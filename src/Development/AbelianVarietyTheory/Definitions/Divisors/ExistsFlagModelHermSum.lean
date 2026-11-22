import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

structure IsRegSurf (p : X ⟶ Sp k) : Prop extends IsArithVar p 1 where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

structure RegCover (p : X ⟶ Sp k) [IsIntegral X] where

  Y : Scheme.{0}

  ρ : Y ⟶ X

  reg : IsRegSurf (ρ ≫ p)

  generic : haveI := reg.isIntegral; ρ (genericPoint Y) = genericPoint X

  finite : haveI := reg.isIntegral; ρ.residueDegree (genericPoint Y) ≠ 0

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

instance : IsIntegral C.Y := C.reg.isIntegral

def deg : ℕ := C.ρ.residueDegree (genericPoint C.Y)

end RegCover

namespace HermLB

end HermLB

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}

def IsFlagCh2 (H : h.IsCInf) (fl : Vert.Flag E r) (a : ℝ) : Prop :=
  h.FlagBcFinite fl ∧ ∃ x : Fin r → ℝ, (∀ i, (grLB fl i H).IsSelfInter (x i)) ∧
    a = ∑ i, x i / 2 - h.flagBc fl / 2

variable (h) in

structure FlagModel extends RegCover p where

  cInf : (h.pull ρ rfl).IsCInf

  flag : Vert.Flag ((Scheme.Modules.pullback ρ).obj E) r

variable (h) in

def IsCh2Deg (a : ℝ) : Prop :=
  Nonempty h.FlagModel ∧ ∀ M : h.FlagModel, IsFlagCh2 M.cInf M.flag (M.deg * a)

end VMetric

variable (p) in

def cxFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℂ))

variable (p) in

def cxFibre.fst : cxFibre p ⟶ X := pullback.fst _ _

variable (p) in

def cxFibre.snd : cxFibre p ⟶ Sp ℂ := pullback.snd _ _

instance cxFibre.algebra : Algebra ℂ Γ(cxFibre p, ⊤) :=
  ((cxFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra

variable (p) in

def cxDeg (E : X.Modules) (r : ℕ) : ℤ :=
  degOfRank ℂ ((Scheme.Modules.pullback (cxFibre.fst p)).obj E) r

theorem cxDeg_congr {E E' : X.Modules} (φ : E ≅ E') (r : ℕ) : cxDeg p E r = cxDeg p E' r :=
  degOfRank_congr ℂ ((Scheme.Modules.pullback _).mapIso φ)

def sqMap {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
  pullback.map A'.hom A'.hom A.hom A.hom φ φ f w.symm w.symm

structure PPAS (S : Scheme.{0}) where

  A : Over S

  [grp : GrpObj A]

  isAb : IsAbelianScheme A

  g : ℕ

  smoothDim : SmoothOfRelativeDimension g A.hom

  c : Pic (A ⊗ A).left

  isPol : IsPrincipalPol A c

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

instance : QuasiSeparated P.A.hom :=
  have := P.isAb.proper
  inferInstance

def ofPolAV (Q : Out.PolAV S) : PPAS S where
  A := Q.A
  isAb := Q.isAb
  g := Q.g
  smoothDim := Q.smoothDim
  c := _
  isPol := IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV Q

theorem isVB_omega : IsVB (omega P.A) P.g := LieVB.isVB_omega P.A P.g

def IsPull (P' : PPAS S') (P : PPAS S) (f : S' ⟶ S) (φ : P'.A.left ⟶ P.A.left) : Prop :=
  ∃ h : IsGrpPullback P'.A P.A f φ, P'.c = CechPic.pull (sqMap h.1.w) P.c

structure RiemannData (y : Sp ℂ ⟶ S) where

  B : Over (Sp ℂ)

  [grp : GrpObj B]

  φ : B.left ⟶ P.A.left

  isPull : IsGrpPullback B P.A y φ

  L : LB B.left

  isLB : L.IsLB

  pol : CechPic.pull (sqMap isPull.1.w) P.c = lam (cls L isLB) (fst B B) (snd B B)

  u : HolUnif B L P.g

  H : Matrix (Fin P.g) (Fin P.g) ℂ

  χ : u.Λ → ℂ

  isAH : u.IsAH H χ

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

def fn (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (z : Fin P.g → ℂ) : ℂ :=
  valR ((d.u.ex z).left ≫ d.φ) W f

def cov (W : P.A.left.Opens) (f : Γ(P.A.left, W)) : Fin P.g → ℂ := fun a =>
  fderiv ℂ (d.fn W f) 0 (Pi.single a 1)

end RiemannData

theorem pull_sqMap_lam {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : Pic A.left) :
    CechPic.pull (sqMap h.1.w) (lam c (fst A A) (snd A A)) =
      lam (CechPic.pull φ c) (fst A' A') (snd A' A') := by
  let m : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A ⊗ A := Over.homMk (sqMap h.1.w) (by
    change sqMap h.1.w ≫ pullback.fst _ _ ≫ A.hom = (pullback.fst _ _ ≫ A'.hom) ≫ f
    rw [sqMap, pullback.lift_fst_assoc, Category.assoc, Category.assoc, h.1.w])
  rw [CechPic.lam_pull_of_isGrpPullback h]
  refine (CechPic.pull_lam m c _ _).trans ?_
  congr 1 <;> refine Over.OverMorphism.ext ?_
  exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]

variable (P : PPAS X)

def IsDualRiemann (t : ℝ) (h : VMetric p (omega P.A) P.g) : Prop :=
  ∀ σ (y : CxPts p σ), Nonempty (P.RiemannData y.1) ∧ ∀ (d : P.RiemannData y.1) (U : X.Opens)
    (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
      (h.met σ).form (dUnit P.A hU f) (dUnit P.A hU f') y =
        form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f')

abbrev IsHodge (h : VMetric p (omega P.A) P.g) : Prop := P.IsDualRiemann Real.pi h

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

variable (P p) [IsIntegral X]

def IsCh2Omega (a : ℝ) : Prop := ∃ h : VMetric p (omega P.A) P.g, P.IsHodge h ∧ h.IsCh2Deg a

def ch2Omega : ℝ := Classical.epsilon (P.IsCh2Omega p)

omit [IsIntegral X] in

def degOmega : ℤ := cxDeg p (omega P.A) P.g

variable {P p} {a b : ℝ}

end PPAS

end GlobalTheory
