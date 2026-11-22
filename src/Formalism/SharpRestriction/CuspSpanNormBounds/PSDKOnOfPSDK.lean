import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm

open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

def InProd (Sg : ℕ → ℕ → Finset D.host.E) : ℕ → List (D.host.E × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => t ∈ Sg (a + 1) s ∧ InProd Sg (a + s) bs

variable {D}

end Arith

end Formalism.MainNotions.S.LocalFrameAxioms

end
