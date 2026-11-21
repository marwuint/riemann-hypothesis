import Formalism.LocalToGlobal.ExponentGrids.EntryG
import Formalism.LocalToGlobal.KernelLattices.ColInst

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section AtRec

open Formalism.DivisionValues (PlOver)

def StdOver {E : Type} [Field E] [NumberField E] {n : ℕ} (g : ℕ) (Lat : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal Lat = stdAt E n P

end AtRec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

def Nd (j : ℕ) : Type := (Q.F j).Cl × (Q.F j).ιV

instance (j : ℕ) : Fintype (Nd Q j) :=
  letI := (Q.hF j).fintypeCl
  inferInstanceAs (Fintype ((Q.F j).Cl × (Q.F j).ιV))

def famRep (j : ℕ) (c : (Q.F j).Cl) : (Q.F j).D c.1 := ((Q.F j).mem c.1).outSec.rep c.2

structure ChBas where

  B : ∀ j (c : (Q.F j).Cl), Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q} (Bb : ChBas Q)

def crd (j : ℕ) (ν : Nd Q j) : (Q.F j).Forms →ₗ[K] K :=
  (Bb.B j ν.1).coord ν.2 ∘ₗ (LinearMap.proj (famRep Q j ν.1)) ∘ₗ ((Q.F j).mem ν.1.1).EqFun.subtype ∘ₗ LinearMap.proj ν.1.1

variable (Q) in

def PthTo : ∀ j : ℕ, Nd Q j → Type
  | 0, _ => Unit
  | j + 1, _ => Σ ν : Nd Q j, PthTo j ν

instance PthTo.fintype : ∀ (j : ℕ) (ν : Nd Q j), Fintype (PthTo Q j ν)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | j + 1, _ =>
    letI := fun ν => PthTo.fintype j ν
    inferInstanceAs (Fintype (Σ ν : Nd Q j, PthTo Q j ν))

variable (Q) in

def MidNd : Type := Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV

instance : Fintype (MidNd Q) :=
  letI := Q.hS.fintypeCl
  inferInstanceAs (Fintype (Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV))

structure LastDat (S₁ : GSD K) (Bsp : Type) [AddCommGroup Bsp] [Module K Bsp] where

  Cl : Type
  [finCl : Fintype Cl]

  pt : Cl → S₁.D

  wt : Cl → ℕ

  V₂ : Type
  [addV : AddCommGroup V₂]
  [modV : Module K V₂]

  ι₂ : Type
  [finι : Fintype ι₂]

  β : S₁.V →ₗ[K] V₂ →ₗ[K] K

  ev : Cl → Bsp →ₗ[K] V₂

  B1 : Cl → Basis S₁.ιV K S₁.V

  B2 : Cl → Basis ι₂ K V₂

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

variable (T : LastDat Q.S₁ Bsp)

variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure ChGood (Q : KerChain K) where

  s : ∀ j b, ((Q.F j).mem b).Sec

  sS : Q.S.Sec

  B : ∀ j, (Q.F j).Cl → Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q : KerChain K} (G : ChGood Q)

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

end Transport

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

abbrev recQ {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
    {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (Am : Amb X)
    (hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K :=
  KerChain.ofCol W Ch sel mu cst L (chKerC W Ch sel mu cst L Am u m2 b hY P hK) hF hE

end Record

end Paths

end Formalism.L2.Ker
