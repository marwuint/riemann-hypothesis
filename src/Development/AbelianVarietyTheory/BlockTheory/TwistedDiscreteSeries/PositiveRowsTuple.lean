import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

end

def AtScale (eps x0 : ℝ) (D : D7) : Prop :=
  ∃ L : SizeData₂ D, L.sc.eps = eps ∧ x0 ≤ L.sc.x ∧ Nonempty (ParameterChoice' D L) ∧ Formalism.MainNotions.SizesAt L

theorem AtScale.mono {eps x0 x1 : ℝ} {D : D7} (h : AtScale eps x1 D) (hx : x0 ≤ x1) : AtScale eps x0 D :=
  let ⟨L, h1, h2, h3⟩ := h
  ⟨L, h1, hx.trans h2, h3⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
