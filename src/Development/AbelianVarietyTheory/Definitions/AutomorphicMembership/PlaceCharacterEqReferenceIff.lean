import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def lvlForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)
    (P : Subgroup G) (ψ : P →* Kˣ) : Set S.Forms := {f | ∀ h : P, r (h : G) f = ((ψ h : Kˣ) : K) • f}

def intForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) : Set S.Forms :=
  {f | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c}

def intSpan (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) : AddSubgroup V :=
  AddSubgroup.closure {y | ∃ a : 𝓞 D.what₂.LL, ∃ x ∈ s, y = D.what₂.embLL (a : D.what₂.LL) • x}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure SideTie (R : RealDat D A Ks) (F : Face D A) (tup : T → D.what₂.Tup) (b : Bool) {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  eE : EE →ₗ[ℂ] R.HE.H

  eE_range : LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e

  eE_norm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eA : ∀ t, S.Amb (tup t) →ₗ[ℂ] (R.HX t).H

  eA_range : ∀ t, LinearMap.range (eA t) =
    Submodule.span ℂ (R.jX t '' lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ)

  eA_norm : ∀ t x, ‖eA t x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eOp_tie : ∀ t x (f : (A.MtildeCSD t).Forms), eA t x = R.jX t f →
    eA t (S.eOp (tup t) x) = R.jX t ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) f)

  iota_tie : ∀ t x, eE (S.iota (tup t) x) = R.Th t (eA t x)

  lat_tie : ∀ t, eA t '' (S.Mtilde (tup t)).carrier =
    R.jX t '' (lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ ∩ intForms (A.MtildeCSD t))

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RowsTieSum (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_sum : ∀ (i : Fin D.R.m) π,
    (⨆ π', ⨆ (_ : ty π' = ty π), D.what₂.isot ((i : ℕ) + 1) π') = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RowsTie (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ty_inj : Function.Injective ty

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_tie : ∀ (i : Fin D.R.m) π, D.what₂.isot ((i : ℕ) + 1) π = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)

namespace SideTie

end SideTie

namespace RowsTieSum

end RowsTieSum

namespace RowsTie

end RowsTie

end GlobalTheory.Mem

end
