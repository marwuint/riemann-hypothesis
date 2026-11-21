import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal ContDiff
open GlobalTheory.CxForm GlobalTheory.ChartGlue GlobalTheory.LineForm

namespace GlobalTheory.FormPartition

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def rd (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

variable {A} in
theorem Good.compat {r : A.ι → V n → ℝ} (h : Good A r) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) : ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [h.2 i j y hi hj, ENNReal.ofReal_mul (by positivity)]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_eq (α : A.Fld) (ε : ℤˣ) :
    A.part α ε = glueMeas A.e fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i y)) := rfl

variable [SecondCountableTopology M]

end GlobalTheory.FormPartition
