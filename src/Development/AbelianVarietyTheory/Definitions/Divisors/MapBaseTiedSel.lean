import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {O : Obj D} {c : ℝ}

def Bundle.TiePins (b : Bundle D O c) (Rr : RealRec b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ RealPins3 b.B.Q ∧ ∃ pins : RealPins b.B.Q, RealRecPins pins Rr

abbrev Bundle.Comparison₂ (b : Bundle D O c) : Type 1 := {Rr : RealRec b.B.Q // b.TiePins Rr}

theorem Bundle.Comparison₂.psi {b : Bundle D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1

theorem Bundle.Comparison₂.pins3 {b : Bundle D O c} (t : b.Comparison₂) : RealPins3 b.B.Q := t.2.2.1

theorem Bundle.Comparison₂.pins {b : Bundle D O c} (t : b.Comparison₂) : RealPins b.B.Q := let ⟨h, _⟩ := t.2.2.2; h

theorem Bundle.Comparison₂.recPins {b : Bundle D O c} (t : b.Comparison₂) : RealRecPins t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h

@[reducible] def Bundle.part (b : Bundle D O c) (t : b.Comparison₂) : Ind.Part D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins

theorem zsc_eq_ind (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) : Ind.zsc P Del h0 c = zsc P Del h0 c := rfl

end Point

abbrev TiedBundle : BdT := fun D O c => Σ b : Bundle D O c, b.Comparison₂

abbrev TiedBundle.base : ∀ D O c, TiedBundle D O c → Bundle D O c := fun _ _ _ b => b.1

abbrev TiedBundle.part : ∀ D O c, TiedBundle D O c → Ind.Part D O c := fun _ _ _ b => b.1.part b.2

section Sel

variable {𝒜 : FamClass}

abbrev TieSel (σ : RawSel Bundle 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂

def compatibleSelection (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel TiedBundle 𝒜 :=
  fun Fm hc x hx i => ⟨σ Fm hc x hx i, τ Fm hc x hx i⟩

def partSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel Ind.Part 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)

theorem map_base_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.base (compatibleSelection σ τ) : RawSel Bundle 𝒜) = @σ := rfl

theorem map_part_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.part (compatibleSelection σ τ) : RawSel Ind.Part 𝒜) = @partSel 𝒜 σ τ := rfl

end Sel

end GlobalTheory.Fc

end
