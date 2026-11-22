import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.SharpRestriction.GlobalTheoremInputs

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

protected abbrev zsc {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  GlobalTheory.Fc.zsc P Del h0 c

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Part (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : RowSideFamily O.ex
  pin : RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : RealTB R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : RealRec B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : RealPins B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : RealRecPins pins Rr

def L3 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)

def ON (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)

def L6 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)

def FUN (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

end GlobalTheory.Fc.Ind

end
