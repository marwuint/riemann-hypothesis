import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Comb

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def lnAdl (A : Adl C Y) (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  lnN (A.m σ) (genAt A.D (under z)) z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ)

end Comb

section Base

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

def LiesUnder (k : s.Comp) (y : Pt s) (x : (Φ.C k).Y.X) : Prop :=
  ∃ p : Sp Qb ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = y.y ∧ (Φ.C k).Carries p y.frame ∧ below p = x

def baseOn (k : s.Comp) (y : Pt s) : (Φ.C k).Y.X := Classical.epsilon (LiesUnder Φ k y)

abbrev basePt (y : Pt s) : (Φ.C (compPt s y)).Y.X := baseOn Φ (compPt s y) y

variable {Φ}

theorem LiesUnder.compPt_eq {k : s.Comp} {y : Pt s} {x : (Φ.C k).Y.X} (h : LiesUnder Φ k y x) : compPt s y = k := by
  obtain ⟨p, hp, -, -⟩ := h
  let o : Sp Qb := IsLocalRing.closedPoint Qb
  refine (PtComp.existsUnique_onComp s (y.y o)).unique (PtComp.onComp_compPt s y o) ?_
  obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  refine ⟨⟨z, hz⟩, fun pt => ?_⟩
  exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨p o, by rw [← hp]; rfl⟩
    (Φ.label k ⟨z, hz⟩ pt)

variable (Φ) in

theorem existsUnique_liesUnder (y : Pt s) : ∃! x, LiesUnder Φ (compPt s y) y x := by
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨⟨k, p⟩, hp, hu⟩ := Φ.lifts Qb y.fK y.y y.y_over y.frame
  obtain rfl : compPt s y = k := LiesUnder.compPt_eq ⟨p, hp.1, hp.2, rfl⟩
  refine ⟨below p, ⟨p, hp.1, hp.2, rfl⟩, ?_⟩
  rintro _ ⟨q, h₁, h₂, rfl⟩
  rw [eq_of_heq (Sigma.mk.inj (hu ⟨_, q⟩ ⟨h₁, h₂⟩)).2]

variable (Φ) in

theorem liesUnder_basePt (y : Pt s) : LiesUnder Φ (compPt s y) y (basePt Φ y) :=
  Classical.epsilon_spec (existsUnique_liesUnder Φ y).exists

end Base

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def rootEx (τ : E →+* ℂ) (i : ℕ) : Letter Dw → ℤ := expo Dw (rootSym Dw (fun _ => false) none τ i)

open Classical in

theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 :=
  Finsupp.sum_single_index (by simp)

def detOmSym (E : Type) [Field E] (g : ℕ) : Sym E →₀ ℤ := ∑ k : Fin g, wholeSym (fun _ => false) none (.inr k : Fin g ⊕ Fin g)

end Roots

structure MetIn {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) : Type where

  hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)

  h0 : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

  r : ∀ k σ, Pts (Φ.C k).Y σ → ℝ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  dir : D.what₂.Tau → Fin N → ℝ

  reg : ∀ k σ, (D.what₂.Tau → Fin N → ℝ) → ℝ → Pts (Φ.C k).Y σ → ℝ

instance {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) : Nonempty (MetIn Φ) :=
  ⟨⟨fun _ _ _ _ => (cxSt _).fsMet _ _ _ fun _ : Unit => 1, fun _ _ _ => (cxSt _).fsMet _ _ _ fun _ : Unit => 1,
    fun _ _ _ => Real.exp 1, fun _ => Adl.triv _ _, 0, fun _ _ _ _ _ => 0⟩⟩

structure Setup (D : D7) : Type 1 where

  A : Amb D

  N : ℕ

  j : ℕ
  indef : 1 ≤ j ∧ j < N

  S : Sig A N j

  κ : Lv A

  s : FinalTheorems S κ

  L : CmList A

  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N

  B : s.Bd L

  fl : s.Comp → D.what₂.Tau → ℂˣ

  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

  ng : NgPkg

  loc : LocSt D N j ng

  glob : GlobSt fun p => (loc.loc p).Mdl

  adm : AdmSt D N j jC

  met : MetIn Φ

namespace Setup

variable {D : D7} (O : Setup D)

def pad : PadPkg D O.N O.j O.s.Comp O.jC O.ng :=
  padAt O.s O.loc O.glob O.adm (flatSt O.s O.Φ O.met.hm) (arIn O.s O.Φ O.met.hm)

def kit (key : KeySec O.s.Xo O.κ.c) : Kit O.s O.L (cxSt D.what₂.LL) O.jC O.ng :=
  ⟨O.Φ, O.dim_eq, key, O.B, O.fl, O.Mb, O.pad, fun _ => Iff.rfl⟩

def Y : DV.ShimX D.what₂.Tau :=
  shimXOfPkg (O.s.cx O.L O.B O.fl) (O.s.alg O.L (cxSt D.what₂.LL) (cutSt _) (resSt _) O.Φ O.dim_eq O.Mb) O.pad O.indef
    O.κ.primes fun _ hp => Nat.prime_of_mem_primeFactors hp

abbrev var (c : O.s.Comp) : Var D.what₂.LL := (O.Φ.C c).Y

abbrev ex (x : DV.Rt D.what₂.Tau O.N) : Letter O.S.Dw → ℤ := rootEx O.S.Dw (DV.tauEmb D x.1) x.2

def adl0 (c : O.s.Comp) (w : Sym D.host.E →₀ ℤ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (fun _ => O.met.h0 c) w

def root0 (c : O.s.Comp) (P : Finset ℕ) (x : DV.Rt D.what₂.Tau O.N) : Adl (cxSt D.what₂.LL) (O.var c) :=
  O.adl0 c (rootSym O.S.Dw (ArIn.ind P) none (DV.tauEmb D x.1) x.2)

def rootH (c : O.s.Comp) (x : DV.Rt D.what₂.Tau O.N) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind ∅) none (DV.tauEmb D x.1) x.2)

def htWt {c : O.s.Comp} (ρ : DV.Rt D.what₂.Tau O.N → Adl (cxSt D.what₂.LL) (O.var c)) (u : D.what₂.Tau → Fin O.N → ℝ)
    (z : (O.var c).X) : ℝ := -∑ x, u x.1 x.2 * (ρ x).ht z

def chg (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : ℝ :=
  ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * lnRatio (O.met.hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) z

def faltAt (c : O.s.Comp) (z : (O.var c).X) : ℝ :=
  (adlOf (O.Φ.C c) (O.met.hm c) (detOmSym D.host.E (D.R.f * O.N))).ht z

structure LatModel (P : Finset ℕ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  line : Finset ℕ → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ → HermLB V.p
  line_spec : ∀ Q ⊆ P, ∀ st, (letterOf O.S.Dw st).isSome →
    V.Induces (O.adl0 c (Finsupp.single (ArIn.ind Q, none, st) 1)) (line Q st) 1

  k : ℕ
  k_pos : 0 < k

  amp : HermLB V.p
  amp_spec : V.Induces (O.met.ab c) amp k

namespace LatModel

variable {O} {P : Finset ℕ} {c : O.s.Comp} (W : O.LatModel P c)

def root (Q : Finset ℕ) (x : DV.Rt D.what₂.Tau O.N) : HermLB W.V.p :=
  if (x.2 : ℕ) < O.j then W.line Q (.inl (DV.tauEmb D x.1, x.2))
  else (W.line Q (.inl (conjEmb (DV.tauEmb D x.1), O.N - 1 - x.2))).dual

def mult : ℕ := W.k * (O.met.ab c).n

def gens (Q : Finset ℕ) : Option (DV.Rt D.what₂.Tau O.N) → HermLB W.V.p := fun o => o.elim W.amp fun x => (W.root Q x).dual

end LatModel

structure IsFlagHeightData (A : SlopeTestRemainingChoices O.Y) : Prop where
  dir : A.dir = O.met.dir
  w : A.w = (O.s.cx O.L O.B O.fl).volC
  ht : ∀ (L : ∀ c, Adl (cxSt D.what₂.LL) (O.var c)) (y : Pt O.s), A.ht L y = (L _).ht (basePt O.Φ y)
  dense : ∀ (c : O.s.Comp) (Z : Set (Pt O.s)), A.dense c Z ↔ Z ⊆ compPt O.s ⁻¹' {c} ∧ Dense (baseOn O.Φ c '' Z)

structure HtIs (H : Ht O.Y) : Prop where
  h0 : ∀ u (y : Pt O.s), H.h0 u y = O.htWt (O.root0 _ ∅) u (basePt O.Φ y)
  int : ∀ y : Pt O.s, y ∈ H.int ↔ below y.y ∉ genBd O.s.T.Z
  hH : ∀ u (y : Pt O.s), y ∈ H.int → H.hH u y = O.htWt (O.rootH _) u (basePt O.Φ y)
  hA : ∀ y : Pt O.s, H.hA y = (O.met.ab _).ht (basePt O.Φ y)
  falt : ∀ y : Pt O.s, y ∈ H.int → H.falt y = O.faltAt _ (basePt O.Φ y)

structure AnIs (c : O.s.Comp) {e : ℕ} {M : Man e} (I : ManIs M (O.var c)) (F : An M D.what₂.Tau O.N) : Prop where
  Z : ∀ a z, z ∈ M.Z a ↔ (O.Φ.C c).π (under (I.pt a z)) ∈ genBd O.s.T.Z
  r : ∀ a z, z ∉ M.Z a → M.r a z = O.met.r c _ (I.pt a z)
  th : ∀ u, I.FormOf (fun x σ => O.met.h0 c σ (O.ex x)) (fun x => -u x.1 x.2) (F.th u)
  a : I.FormOf (fun (_ : Unit) σ => (O.met.ab c).m σ) (fun _ => (((O.met.ab c).n : ℕ) : ℝ)⁻¹) F.a
  ph : ∀ u a z, z ∉ M.Z a → F.ph u a z = O.chg c none u _ (I.pt a z)
  phR : ∀ R : ℝ, 2 ≤ R → ∀ u a z, F.phR R u a z = O.chg c (some R) u _ (I.pt a z)
  phS : ∀ u (s : ℝ), 0 < s → ∀ a z, F.phS u s a z = O.met.reg c _ u (Real.exp (-(s ^ 2)⁻¹)) (I.pt a z) / 2

structure PtsIs {T : Real0 O.Y} (I : ∀ c, ManIs (T.M c) (O.var c)) (P : T.Pts) : Prop where
  conj : ∀ y : Pt O.s, (I _).Lists (basePt O.Φ y) (P.conj (compPt O.s y) y)
  ar : ∀ B (y : Pt O.s) g, (T.M (compPt O.s y)).Smooth g → P.ht B _ y ((T.K B (compPt O.s y)).ar g) = P.mean _ y g
  L : ∀ B : ℝ, 2 ≤ B → ∀ (y : Pt O.s) u, P.ht B (compPt O.s y) y (T.L B _ u) =
    O.htWt (O.root0 _ (FlagAr.setB O.Y B)) u (basePt O.Φ y)
  a : ∀ B : ℝ, 2 ≤ B → ∀ y : Pt O.s, P.ht B (compPt O.s y) y (T.a B _) = (O.met.ab _).ht (basePt O.Φ y)

def NumIs {T : Real0 O.Y} {c : O.s.Comp} (I : ManIs (T.M c) (O.var c)) (B : ℝ) (W : O.LatModel (FlagAr.setB O.Y B) c) : Prop :=
  ∀ ε π, W.V.IsDown I ε π → (T.K B c).NumOn ε π W.V.ν (W.gens (FlagAr.setB O.Y B)) (T.gen B c W.mult)

structure Reads (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) : Type 1 where
  aux : O.IsFlagHeightData A
  ht : O.HtIs H

  man : ∀ c, ManIs (T.M c) (O.var c)
  an : ∀ c, O.AnIs c (man c) (T.F c)

  pts : T.Pts
  pts_is : O.PtsIs man pts

  mdl : ∀ (P : Finset ℕ) (c : O.s.Comp), O.LatModel P c
  num : ∀ B : ℝ, 2 ≤ B → ∀ c, O.NumIs (man c) B (mdl _ c)

def aux (Ps : ℝ → O.s.Comp → MvPolynomial (Option (D.what₂.Tau × Fin O.N)) ℝ) : SlopeTestRemainingChoices O.Y where
  dir := O.met.dir
  w := (O.s.cx O.L O.B O.fl).volC
  Ps := Ps
  ht (L : ∀ c, Adl (cxSt D.what₂.LL) (O.var c)) (y : Pt O.s) := (L _).ht (basePt O.Φ y)
  dense (c : O.s.Comp) (Z : Set (Pt O.s)) := Z ⊆ compPt O.s ⁻¹' {c} ∧ Dense (baseOn O.Φ c '' Z)

end Setup

end GlobalTheory.Mean4O
