import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

def SatU {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) : Prop :=
  T = TwDat.untw B T.pl → ∀ v v', OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt

def ExistsUnlocalizedSaturatedState : Prop := StepW Start fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), SatU P ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure SameGal (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  pl : HEq D.naut.plGw D'.naut.plGw

structure Carried (D D' : D7) : Prop where
  exp : SameExport D D'
  emb : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (x : D.LL0) (x' : D'.LL0),
    D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      HEq (D.ntw.emb0 i x) (D'.ntw.emb0 i' x') ∧ HEq (D.ntw.emb0b i x) (D'.ntw.emb0b i' x')

structure Seed (D : D7) (A : D.ntw.Tw → Finset (PlE D.host)) where
  s : D.what₂.places.Pl → D.ntw.Tw
  reads : ∀ v, ∃ b, ReadsAt (s v) b v
  conj : ∀ v, s (D.what₂.places.conj v) = s v
  same : ∀ v v', TwistedAt D v → TwistedAt D v' → OverOne D v v' → s v' = s v
  xd : ThData D
  all : XdAll xd
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)
  Q : D.ntw.Tw → Finset (PlE D.host)
  k : D.ntw.Tw → ℕ
  ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ
  good : ∀ v, TwistedAt D v → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (s v) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (s v)) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (s v) (twEps D (s v)) (S (s v)) (A (s v)) (Q (s v)) (k (s v)) (ψ (s v) ^ a)
  sep : ∀ v v', TwistedAt D v → TwistedAt D v' → s v ≠ s v' → Disjoint (Q (s v)) (Q (s v'))

def Seed.pack {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) (v : D.what₂.places.Pl) : TwPack D :=
  ⟨σ.s v, σ.Q (σ.s v), σ.k (σ.s v), σ.ψ (σ.s v)⟩

def TwFrom (X : Stages) {A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)} (σ : Seed X.toD7 A) {B' : Base} (h : Enl X.B B')
    (T' : TwDat B') : Prop :=
  (∀ (v' : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar v' ^ T'.k v' = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
  ∀ v' : B'.places.Pl,
    (TwistedAt X.toD7 (plUnder h v') →
      HEq (T'.Q v') (σ.Q (σ.s (plUnder h v'))) ∧ T'.k v' = σ.k (σ.s (plUnder h v')) ∧
      ∃ (ι : RootIso X.toD7 (σ.s (plUnder h v')) (σ.k (σ.s (plUnder h v')))) (χ : HChar X.toD7.host.E),
        FrobPick (σ.s (plUnder h v')) _ _ (σ.ψ (σ.s (plUnder h v'))) ι χ ∧ HEq (T'.psi v') χ) ∧
    (¬ TwistedAt X.toD7 (plUnder h v') → T'.psi v' = 1)

def BareK : Prop := StepW Start fun K B' f' _ w' => ∀ (P' : Pre2 K w') (X : Stages) (f : Fr X.B.toPre), B'.toPre = X.B.toPre →
  HEq f' f → GrpTrue X.N f → ∃ x' : St P', IsEmpty x'.o.N.nd.Loc ∧ SameGal X.toD7 (Dof x')

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

end GlobalTheory.HeightCounting.Up

end
