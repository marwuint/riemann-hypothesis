import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

def RegEl (G : HTGroup p) (y : G.Cˣ) : Prop :=
  (minpoly G.F (y : G.C)).natDegree = G.n ∧ (minpoly G.F (y : G.C)).Separable

def pairOf {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKCx
