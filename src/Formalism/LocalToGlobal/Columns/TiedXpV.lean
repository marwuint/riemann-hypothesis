import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.TiedValLat
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (ΛM : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)

structure PCrd (σ₀ : X.K →+* ℂ) extends
    StepCrd Pr σ₀ (R.N R.m - 1) (fun c : (ptGSD W ΛM).Cl => ((ptGSD W ΛM).outSec.rep c).1.N) where
  lt : X.Tau → DomWeight (R.N R.m - 1)
  hlt : lt = W.sgTrue

variable (hc : CMData X.F X.E) (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (hS : DecoPtSurj hc (R.N R.m - 1) (∅ : Finset (Pl X.E)) Pr.vGs)

namespace XpV

end XpV

end GenP

section Rec

variable {d : ColDat} (a : ColArgs d)

def RowSame (d : ColDat) : Prop := ∀ u τ, RowPar.of (d.hcW u τ) = RowPar.of (d.hcW d.u₀ τ)

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word)

end Rec

end Formalism.L2.Col
