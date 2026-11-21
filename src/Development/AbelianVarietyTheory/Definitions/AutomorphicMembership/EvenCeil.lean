import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

noncomputable section

namespace GlobalTheory.Mem.Num

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits

def evenCeil (y : ℝ) : ℕ := 2 * ⌈y / 2⌉₊

variable (C : FC) (s : Scale) (n : ℕ)

def eAt : ℕ := Nat.clog 2 ⌈s.x ^ (2 + 8 * s.eps)⌉₊

def fAt : ℕ := 2 * n

def mAt : ℕ := evenCeil (Real.sqrt (s.x * s.delta1))

def kAt : ℕ := evenCeil (s.x ^ (9 / 2 + 10 * s.eps))

def rAt : ℕ := kAt s + mAt s - 1

def nWAt : ℕ := 8 * ⌈C.P.CnW * (rAt s : ℝ) * ((fAt n : ℝ) + (fAt n : ℝ) ^ 2 * ((kAt s : ℝ) - 1) ^ 3 * s.L ^ 2 / (mAt s : ℝ)) / 8⌉₊

def nPAt : ℕ := 8 * fAt n * rAt s + 4

def TOAt : ℕ := ⌈s.x ^ C.T.cTO⌉₊

def tAt : ℕ := TOAt C s * nWAt C s n + nPAt s n - rAt s

def cStar : ℝ := max (max C.P.CDel C.P.CCount) (max C.P.Ch0N 7)

def cP : ℝ := 7 * C.T.eP - 1

def cDel : ℝ := (C.Ct + 5) * cStar C + cStar C * (C.P.CF + 6) + 2 * C.Ct + 10

def cLam : ℝ := max (3 * C.Ct + 6) (cDel C + 17) + 1

def cH : ℝ := max (max (max (cLam C + 1) ((C.Ct + 5) * cStar C)) (max (cStar C * (C.Ct + 1) + 6) (3 * C.Ct + 7)))
  (max (cP C + C.T.cTO + C.Ct + 30) 100)

def DelAt : ℕ := ⌈s.x ^ cDel C⌉₊

def ScAt : ℝ := (kAt s : ℝ) * (4 * (DelAt C s : ℝ))

def LwAt : ℕ := 10 * ⌈(C.Ct + 4) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def YAt : ℝ := ((kAt s : ℝ) * s.b) ^ 8

section Places

variable {R : Ranks} (H : Host R) (a b : R.A → ℤ)

instance psiFin (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

end Places

end GlobalTheory.Mem.Num

end
