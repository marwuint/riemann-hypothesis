import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

def plF (D : D7) (w : D.what₂.places.Pl) : slopeLatticeData.FinPl D.what₂.LL := ⟨(D.plEq w).asIdeal, (D.plEq w).isMaximal⟩

def plB (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) : D.what₂.places.Pl :=
  D.plEq.symm ⟨z.1, z.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField z.2 (RingOfIntegers.not_isField D.what₂.LL)⟩

variable {D : D7} (L : SizeData₂ D)

def prOf : Finset ℕ :=
  L.supp.image D.what₂.places.resChar ∪ Finset.univ.image (fun u : D.what₂.Word => (D.mem u).A.T)

def SOf : Finset (slopeLatticeData.FinPl D.what₂.LL) := (prOf L).biUnion (fun p => LChain2.plOver D.what₂.LL p)

def sgZ (u : D.what₂.Word) : slopeLatticeData.FinPl D.what₂.LL →₀ ℤ :=
  Finsupp.onFinset (SOf L) (fun z => if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ else 0)
    (fun z hz => by by_contra h; exact hz (if_neg h))

def tauZ : slopeLatticeData.FinPl D.what₂.LL →₀ ℤ :=
  Finsupp.onFinset (SOf L) (fun z => if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ else 0)
    (fun z hz => by by_contra h; exact hz (if_neg h))

open Classical in

def ioPr (p : ℕ) : ℝ := if h : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p then L.io h.choose else 0

structure Mx (D : D7) where
  v : InfinitePlace D.what₂.LL
  Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ
  Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ
  Ball : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (D.div.Nu u).ι ℂ
  γ : D.what₂.Word → ℝ
  Bf : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) ((D.fm u).lat 0).ι ℂ
  Vr : ∀ u, Matrix ((D.fm u).lat 0).ι (D.div.Nu u).ι ℂ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

def fam0 (m : ℕ) (A : Mx D) : LChain2.Fam D.what₂.Word m where
  K := D.what₂.LL
  Wd := Module.Dual D.what₂.LL D.div.RR.V
  κ := D.div.RR.ι
  κ₁ := Fin (D.what₂.Dall - D.what₂.Drows)
  V := fun u => (D.div.Nu u).V
  ι := fun u => (D.div.Nu u).ι
  Vf := fun u => ((D.fm u).lat 0).V
  ιf := fun u => ((D.fm u).lat 0).ι
  b' := D.div.RR.dualB
  X' := D.div.RR.dualX
  cc := D.div.RR.dualL
  b := fun u => (D.div.Nu u).b
  X := fun u => (D.div.Nu u).X
  M := fun u => DV.MramL D u
  N0 := fun u => L.NuLat u
  bf := fun u => ((D.fm u).lat 0).b
  Xf := fun u => ((D.fm u).lat 0).X
  Mf := fun u => ((D.fm u).lat 0).L
  σ := sgZ L
  τ := tauZ L
  B := D.div.Bk
  v := A.v
  Y := A.Y
  Y' := A.Y'
  Ball := A.Ball
  γ := A.γ
  Bf := A.Bf
  Vr := A.Vr
  S := SOf L
  gain := fun j z => L.gainD (j.val + 1) (plB D z)
  Fj := fun j z => L.F (j.val + 1) (plB D z)
  Ej := fun u j z => L.E u (j.val + 1) (plB D z)
  iop := ioPr L
  T := fun u => (D.mem u).A.T
  h := D.div.h
  lam := fun _ => 0
  Dstar := D.what₂.Dstar
  η0 := A.η0
  η1 := A.η1
  e0 := A.e0

def lamOf (m : ℕ) (A : Mx D) (u : D.what₂.Word) : ℝ :=
  ((fam0 L m A).ST u).fold max 0 (fun z => (fam0 L m A).lenR u z / (fam0 L m A).dM u)

def famOf (m : ℕ) (A : Mx D) : LChain2.Fam D.what₂.Word m := { fam0 L m A with lam := lamOf L m A }

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

structure FieldEq {U0 : Type} {W : U0 → Type} {Top Top' : Type} {m f f' : ℕ} (A : Data U0 W Top m f)
    (B : Data U0 W Top' m f') (eT : Top ≃ Top') (eF : Fin f ≃ Fin f') : Prop where
  x : A.x = B.x
  ε : A.ε = B.ε
  a : A.a = B.a
  b : A.b = B.b
  b' : A.b' = B.b'
  k : A.k = B.k
  L : A.L = B.L
  La : A.La = B.La
  B0 : A.B0 = B.B0
  Nc : A.Nc = B.Nc
  gam : A.gam = B.gam
  LpL : A.LpL = B.LpL
  v : A.v = B.v
  lg : A.lg = B.lg
  aT : ∀ t, A.aT t = B.aT (eT t)
  w : ∀ u0 j ρ, A.w u0 j ρ = B.w u0 j (eF ρ)
  d : ∀ u0 u, A.d u0 u = B.d u0 u
  T : ∀ u0 u, A.T u0 u = B.T u0 u
  muN : ∀ u0 u, A.muN u0 u = B.muN u0 u
  muMaxN : ∀ u0 u, A.muMaxN u0 u = B.muMaxN u0 u
  h : ∀ u0 u, A.h u0 u = B.h u0 u
  muM : ∀ u0 u, A.muM u0 u = B.muM u0 u
  muMaxM : ∀ u0 u, A.muMaxM u0 u = B.muMaxM u0 u
  EeJ : ∀ u0 u j, A.EeJ u0 u j = B.EeJ u0 u j
  muCC : ∀ u0, A.muCC u0 = B.muCC u0
  muMinCC : ∀ u0, A.muMinCC u0 = B.muMinCC u0
  Fo : ∀ u0, A.Fo u0 = B.Fo u0
  Ga : ∀ u0, A.Ga u0 = B.Ga u0
  Ta : ∀ u0, A.Ta u0 = B.Ta u0
  ASK : ∀ u0, A.ASK u0 = B.ASK u0
  IO : ∀ u0, A.IO u0 = B.IO u0
  HH : ∀ u0, A.HH u0 = B.HH u0
  del : ∀ u0, A.del u0 = B.del u0
  η : ∀ u0, A.η u0 = B.η u0
  e : ∀ u0, A.e u0 = B.e u0
  delBar : A.delBar = B.delBar
  etaBar : A.etaBar = B.etaBar
  eBar : A.eBar = B.eBar

variable {eps : ℝ} (Fm : FamP eps) (x : ℝ)

variable {Fm x}

end Family

end Formalism.L2.GlobalTheoryTheory.FamRec

end
