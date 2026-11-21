import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

def numWords (C : FC) (s : Scale) (R : Ranks) : ℕ :=
  ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
