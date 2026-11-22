import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (fun ρ => ((Wc D i).sig (tauE D ρ)).1) (fun ρ => ((Wc D i).sig (tauE D ρ)).2)
    (fun ρ => aPl D i ((Wc D i).sig (tauE D ρ)).1 (lab σ ρ))
    (fun ρ => aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (lab σ ρ))

section Conj

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

def EtaAt (η' : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η' ∧ ResEta D η' 1 ∧ (∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ (k : D.host.Eˣ) (x : (AE D)ˣ),
      (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E) → ∃ y : D.what₂.LL,
        D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ) ∧
        σ y = ((η' x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ)

def ResAt (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ PP ∈ R.Pg, ∀ u, ∃ y : D.what₂.LL,
    D.what₂.embLL y = ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∧ σ y = ((χ' PP u : ℂˣ) : ℂ)

def datV (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q A.μ0) (LevelP.triv _ _ _) (fun _ => χ') (R.xiR A.μ0) Frm.A

def valAt (x : A.fam.amb.FL i A.μ0) (c : (A.MtCSD i A.μ0).Cl) : (A.MtCSD i A.μ0).V :=
  ((show (A.MtCSD i A.μ0).Forms from x) : (A.MtCSD i A.μ0).Cl → (A.MtCSD i A.μ0).V) c

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure ConjLift where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  chi : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ

  cV : CoefA (Vc D i)

  coef : (A.MtCSD i A.μ0).V →ₛₗ[σ] cV.W

  HV : HMod (Bridge.Gf (Vc D i) → cV.W)

  jV : A.fam.amb.FL i A.μ0 →ₛₗ[σ] HV.H

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  io : LowT (R.MW i σ) →ₗ[ℂ] cV.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  thF : HV.H →ₗ[ℂ] MMap (R.MW i σ)

  thG : HV.H →ₗ[ℂ] (R.HW i σ).H

namespace ConjLift

variable {R i σ} (Y : ConjLift R i σ)

def pt : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) Y.BW Y.vec

def extV : Y.HV.H →ₗ[ℂ] (GA D (Vc D i) → Y.cV.W) := Y.cV.ext ∘ₗ Y.HV.e

abbrev lev : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (datV R i Y.chi)

structure IsChr : Prop where
  mu : ChiAt R i σ Y.mu
  eta : EtaAt R σ Y.eta
  chi : ResAt R i σ Y.chi

structure IsSrc : Prop where
  cV : Y.cV.Is
  coef_li : LinearIndependent ℂ fun a => Y.coef ((A.MtCSD i A.μ0).bV a)
  coef_span : Submodule.span ℂ (Set.range fun a => Y.coef ((A.MtCSD i A.μ0).bV a)) = ⊤
  coef_pair : ∀ a b, inner ℂ (Y.coef ((A.MtCSD i A.μ0).bV a)) (Y.coef ((A.MtCSD i A.μ0).bV b)) =
    σ ((A.MtCSD i A.μ0).pair ((A.MtCSD i A.μ0).bV a) ((A.MtCSD i A.μ0).bV b))
  coef_rat : ∀ (γ : GQ (Vc D i)) (x x' : (A.MtCSD i A.μ0).V),
    (R.B.L i A.μ0).pres.coef x' = (R.cV i).coef.ρ γ ((R.B.L i A.μ0).pres.coef x) → Y.coef x' = Y.cV.coef.ρ γ (Y.coef x)
  HV : Y.HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) Y.cV.coef.ρ Y.lev.J Y.lev.χ)
    (Bridge.adInner (Bridge.ratF (Vc D i)) Y.lev.J (R.B.L i A.μ0).pres.y)
  jV : ∀ x c, Y.HV.e (Y.jV x) ((R.B.L i A.μ0).pres.y c) = Y.coef (valAt i x c)

structure IsLift : Prop where
  om : IsWeilDatumO R.ψ (Vc D i) (Wc D i) Y.mu (Y.mu * Y.eta⁻¹) Y.om
  BW : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (Y.BW ρ) ((Wc D i).sig (tauE D ρ)).1
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q A.μ0) (R.xiR A.μ0) Y.vac Y.vec
  pt : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Y.pt P)
  io : IsIoW R.θ (R.MW i σ) Y.cV Y.om Y.pt (deltaAtEmb i σ) Y.io
  thF_mem : ∀ x, Y.thF x ∈ R.Wall i σ
  thF : ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h f => thetaKO Y.om h g f) Y.pt Y.io
      (LinearMap.range Y.extV) thP ∧
    ∀ x (v : ∀ ρ, lowT (R.MW i σ) ρ),
      Y.thF x (fun ρ => v ρ) = thP (Y.extV.rangeRestrict x) (PiTensorProduct.tprod ℂ v)
  thG : ∀ x, (R.HW i σ).e (Y.thG x) = postOn _ (R.eWf i σ) (Y.thF x)

structure Is : Prop where
  chr : Y.IsChr
  src : Y.IsSrc
  lift : Y.IsLift

end ConjLift

end Conj

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL
