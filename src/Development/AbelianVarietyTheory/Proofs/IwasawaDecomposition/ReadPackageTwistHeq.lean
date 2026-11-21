import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

section Gen

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem eigAd_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {Sb eig} (h : EigAd Y Sb eig)
    (v : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) → (R.HW i (sg0 D A3.A)).H) (H : ∀ i y, Y.mj.eW i y = v i y)
    (i : Fin D.R.m) (σ k P α Rr) (hd : HkDat R Sb i k P α Rr) (hg : D.nd.goodRow σ) (y) (hy : y ∈ D.what₂.isot (i.1 + 1) σ) :
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (v i y)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (v i y) := by
  rw [← H]
  exact h i σ k P α Rr hd hg y hy

end Gen

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}

abbrev RdTw (x : St P) (N : TwNew (Dof x)) : Type 1 :=
  R3.Read (datTw x N).R.toRealDat (datTw x N).F.lv2 (sideTw x N).p0

def jMtB (Y : RdTw x N) (μ h i y) : type_of% (x.r.Y.IL.jMt μ h i y).1 := (by with_unfolding_all exact ((Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))

def mtAd (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) {M : MtFam (Dof x)} (a : MtAd x.r.Y M) :
    MtAd Y (N.mt M) where
  PV i := ⟨(by with_unfolding_all exact ((a.PV ((i))).ψ : _)), (by with_unfolding_all exact ((a.PV ((i))).inj : _)), (by with_unfolding_all exact ((a.PV ((i))).into : _)), (by with_unfolding_all exact ((a.PV ((i))).onto : _))⟩
  std := (by with_unfolding_all exact (a.std :))
  eW := (by with_unfolding_all exact (a.eW :))
  read μ h i y g := (by with_unfolding_all exact (((a.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))).trans
    (congrFun (H ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (((a.PV ((i))).ψ ((g))) : _))))) :))
  rat := (by with_unfolding_all exact (a.rat :))
  wt := (by with_unfolding_all exact (a.wt :))
  id := (by with_unfolding_all exact (a.id :))

def eWB (Y : RdTw x N) (i y) : type_of% (x.r.Y.mj.eW i y) := (by with_unfolding_all exact ((Y.mj.eW ((i)) ((y))) : _))

theorem hkDat {Sb i k Q α Rr} (h : HkDat (datTw x N).R Sb i k Q α Rr) :
    HkDat x.m.z.R ((Sb)) ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigAd (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) {Sb eig} (h : EigAd x.r.Y Sb eig) :
    EigAd Y ((Sb)) ((eig)) := fun i σ k Q α Rr hd hg y hy =>
  (by with_unfolding_all exact ((eigAd_of h (((eWB Y))) ((H)) ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((hkDat hd))) ((hg)) ((y)) ((hy))) : _))

def inRat (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) (n : InRat x.r.Y x.m.z.cG) : InRat Y (datTw x N).cG where
  kKs := (by with_unfolding_all exact (n.kKs :))
  hk := (by with_unfolding_all exact (n.hk :))
  In := (by with_unfolding_all exact ((ratIn N n.In) :))
  rat :=
    { hecke := fun j k Q α Rr h1 h2 hd y => (by with_unfolding_all exact ((n.rat.hecke j k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) h1 ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact ((hkDat hd) :))) ((by with_unfolding_all exact (y :)))) :))
      eig := (by with_unfolding_all exact ((eigAd Y H n.rat.eig) :))
      Sb_le := (by with_unfolding_all exact (n.rat.Sb_le :))
      lvl := (by with_unfolding_all exact (n.rat.lvl :))
      psi := (by with_unfolding_all exact (n.rat.psi :)) }

def inMt (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) (n : InMt x.r.Y (cfOf x) w.I.xi (QOf P)) :
    InMt Y ((N.cf (cfOf x))) w.I.xi (QOf P) where
  M := (by with_unfolding_all exact ((N.mt n.M) :))
  ad := (by with_unfolding_all exact ((mtAd Y H n.ad) :))
  mt := (by with_unfolding_all exact ((mtIn N n.mt) :))

end GlobalTheory.HeightCounting.Up.LiTw

end
