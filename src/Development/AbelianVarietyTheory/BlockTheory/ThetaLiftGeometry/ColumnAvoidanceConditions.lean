import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV

@[reducible] def fieldsOf (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def primesOf (D : D7) (EX : ErrX D) : Primes (fieldsOf D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  ftWord := D.wordFin
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def wtsOf (D : D7) (EX : ErrX D) : Wts (fieldsOf D) (primesOf D EX).Word D.R where
  row τ := RowPar.of (D.hc τ)
  hc := D.hcW
  tops := topsOf D.host D.eTau

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

end
