import Mathlib

open Finset

noncomputable section

namespace Formalism.CL

variable (p : ℕ) [Fact p.Prime]

def phiPoly : Polynomial ℚ_[p] :=
  Polynomial.X ^ p - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ (p - 1) + Polynomial.C (p : ℚ_[p])

def phiIter (g : ℕ) : Polynomial ℚ_[p] := (fun f => (phiPoly p).comp f)^[g] Polynomial.X

def uu (g : ℕ) : PowerSeries ℚ_[p] :=
  (p : ℚ_[p])⁻¹ • ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

end Formalism.CL
