import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelEquivCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.FieldBC GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem isBC_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    IsBC hle (rulBC hle f) (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f) := by
  intro S _ _ _ h y
  rw [((_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 S h y]
  simp

end Field

section Action

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : actLev c lev g f ∈ sec Xo c a n :=
  actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

end Action

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} {i : Fin D.R.m}

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

section Second

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Y : RowDat T G i) (R : RealDat D A Ks)

def phiSmall (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) Y.dict (muPin (Wc D i) Y.dict Y.mu cc) (rdU Y.U f)

end Second

variable [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0}

variable {O : OMDat T.toCore R i Tp tup} {Y : RowDat T G i}

theorem phi_eq (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiSmall Y cc f := rfl

end Compare

end GlobalTheory.LevelEquivCompare
