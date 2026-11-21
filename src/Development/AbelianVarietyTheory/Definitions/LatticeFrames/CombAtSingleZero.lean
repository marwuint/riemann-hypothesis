import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def CombAt (P : Pl D → Prop) {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, MxAt P u

def extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) (c : WO A T →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resS T).symm (u, 0)

def extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c : WO S A →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resT S).symm (u, 0)

def kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w : WO S L'') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)

def lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) : WO A S → WO S X → ℂ :=
  fun u => o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))

def BiVacAt (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A') (P : Pl D → Prop)
    (C : WO A S → WO S A' → ℂ) : Prop :=
  (∀ v, Vac ψ A S LA LS P fun u => C u v) ∧ ∀ u, Vac ψ S A' LS LA' P (C u)

variable {u : D.what₂.Word}

def xiBF (d : Dat D u) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (a : GA D (d.st (j + 1)).V) : WO (d.bes j ρ h).V₀ (D.sp.X (j + 1)) → ℂ :=
  flatBF (d.sBF j ρ h) ((d.p j).ω (d.t j, a * d.t (j + 1)) ((d.p j).pt P₁))

def xiTop (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) : WO (D.sp.X (j + 1)) D.sp.X' → ℂ :=
  fun w => (d.pT j h).ω (d.t (j + 1), 1) ((d.pT j h).pt P₂) ((d.jac j 0 h).d.ext0 D.sp.X' w)

structure OffDat (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where

  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (d.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (d.st j).V

  M : ∀ j ρ h, Lat (d.bes j ρ h).V₀

  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E

  ζ₀ : Fin d.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {d : Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffDat d k ι)

namespace OffDat

def atT (v : Pl D) : Prop := ∃ i, v = (o.p i).v

end OffDat

variable {o} {Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)}

namespace OffTest

theorem combAt_single_zero (P : Pl D → Prop) {S T : HSp D} (c : ℂ) : CombAt P (Finsupp.single (0 : WO S T) c) := by
  intro u hu
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
  intro i j
  exact Submodule.zero_mem _

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb]
  exact GlobalTheory.MixPer.heisO_zero ψ S T f

end OffTest

end GlobalTheory.FinPl

end
