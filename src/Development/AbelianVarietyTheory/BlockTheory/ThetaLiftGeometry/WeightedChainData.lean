import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

def cpy (E : Type) [Field E] (a b : ℕ) : Sp E a →ₗ[E] Sp E b :=
  LinearMap.pi fun l : Fin b => atNL E a l.1

structure ChainData (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  X : Fields
  s : Seam D X
  Pr : Primes X

  w : Pr.Word
  Ch : Chars X Pr D.R.m

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  S : Set ℕ

  xi : Tup X.F X.E X.K S
  cst : LocCst X (rowSG Pr sel xi)
  L : ChIdx X Pr D.R (QE sel (xi : Chr X.F X.E X.K))
  G : ChGlob X D.R.m
  δ : ℂ
  B : Base D D.host.ccK δ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  O : GL3Theta.LiftObj D (D.chTw u μ)

  lamTop : rowSG Pr sel xi → Submodule (𝓞 X.E) (Sp X.E (D.R.N D.R.m - 1 + 0))

  depth : rowSG Pr sel xi → ℕ

  rep : ∀ i, (D.chTw u μ).cls i →
    Option (L.β i) × DecoF X.E (D.R.N i) (Pr.vT w) ∅ (rowSG Pr sel xi) × Set (Sp X.E (D.R.N i))

namespace ChainData

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev SB : Finset (HeightOneSpectrum (𝓞 T.X.E)) := rowSG T.Pr T.sel T.xi

abbrev Pt (i : ℕ) : Type := DecoF T.X.E (D.R.N i) (T.Pr.vT T.w) ∅ T.SB

abbrev Lab (i : ℕ) : Type := Option (T.L.β i) × T.Pt i × Set (Sp T.X.E (D.R.N i))

abbrev AutX (i : ℕ) : Type := Sp T.X.E (D.R.N i) ≃ₗ[T.X.E] Sp T.X.E (D.R.N i)

abbrev XP : Type := Sp T.X.E (D.R.N D.R.m - 1 + 0)

open Classical in

def Jtop (P : T.SB) : Subgroup (T.XP ≃ₗ[T.X.E] T.XP) :=
  if P.1 ∈ T.Pr.vGs then
    (if T.cst.sharp then LocE.JGsym P.1 (qOf P.1) D.R.k D.R.rS D.R.r D.R.t (D.R.N D.R.m - 1) 0
      else LocE.JG P.1 (qOf P.1) D.R.k D.R.r D.R.t (D.R.N D.R.m - 1) 0)
  else LocE.JQ P.1 (qOf P.1) D.R.r (D.R.N D.R.m - 1) 0

open Classical in

def lamM (P : T.SB) (h : T.XP ≃ₗ[T.X.E] T.XP) : T.X.K :=
  if P.1 ∈ T.Pr.vGs then
    (if T.cst.sharp then
        LocE.lamGBS (qOf P.1) (psi0P T.Ch P.1) (chiP T.Ch P.1) D.R.k D.R.r D.R.t D.R.m (D.R.N D.R.m - 1) 0 h.toLinearMap
      else LocE.lamGB (qOf P.1) (psi0P T.Ch P.1) (chiP T.Ch P.1) D.R.k D.R.r D.R.t D.R.m (D.R.N D.R.m - 1) 0 h.toLinearMap)
  else LocE.lamQB (resChar (T.xi : Chr T.X.F T.X.E T.X.K) P.1) D.R.r (D.R.N D.R.m - 1) h.toLinearMap

open Classical in

def InTopLat (i : ℕ) (P : T.SB) (y : Sp T.X.E (D.R.N i)) : Prop :=
  cpy T.X.E _ _ y ∈ (if P.1 ∈ T.Pr.vGs then stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1 else T.lamTop P) ∧
    IntAt P.1 (atNL T.X.E (D.R.N i) (D.R.N D.R.m - 1) y)

open Classical in

def InTopCong (i : ℕ) (P : T.SB) (k : T.AutX i) : Prop :=
  (∀ y, T.InTopLat i P (k y) ↔ T.InTopLat i P y) ∧
    ∀ y, T.InTopLat i P y →
      T.InTopLat i P ((((qOf P.1 : ℕ) : T.X.E) ^ (if P.1 ∈ T.Pr.vGs then 1 else T.depth P))⁻¹ • (k y - y))

def TopTie : Prop :=
  ∀ P : T.SB, P.1 ∉ T.Pr.vGs →
    localization₂ P.1.asIdeal (T.lamTop P) = T.lamTop P ∧ (∀ j ∈ T.Jtop P, ∀ x ∈ T.lamTop P, j x ∈ T.lamTop P) ∧
    (∀ x ∈ stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1, (((qOf P.1 : ℕ) : T.X.E) ^ D.R.m) • x ∈ T.lamTop P) ∧
    (∀ x ∈ T.lamTop P, (((qOf P.1 : ℕ) : T.X.E) ^ D.R.m) • x ∈ stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1) ∧
    4 * D.R.m + 1 ≤ T.depth P ∧ 2 * D.R.m + 2 * T.cst.M ≤ T.depth P

end ChainData

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData
