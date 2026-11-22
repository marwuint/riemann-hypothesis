import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

namespace Model

def l0 : Fin 3 → ℝ := ![Real.log 2, Real.log 3, Real.log 211]
def gain0 : Fin 1 → Fin 3 → ℝ := fun _ => ![1, 0, 0]
def F0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 2
def E0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 4
def tau0 : Fin 3 → ℝ := ![1 / 2, 0, 0]
def io0 : Fin 3 → ℝ := ![1 / 10, 0, 0]
def len0 : Fin 3 → ℝ := ![3 / 5, 0, 1 / 20]
def sg0 : Fin 3 → ℝ := fun w => UnitWeightPartition.sgw Finset.univ gain0 F0 E0 w - ![1 / 10, 0, 0] w
def iop0 : ℕ → ℝ := fun p => if p = 2 then 1 / 10 else 0
def SgV : ℝ := UnitWeightPartition.Sg Finset.univ l0 sg0 tau0
def BeV : ℝ := UnitWeightPartition.BeSum Finset.univ l0 1 len0 tau0
def IOV : ℝ := ∑ p ∈ ({2, 3, 211} : Finset ℕ), Real.log (p : ℝ) * iop0 p
def EeV : ℝ := 2 * ∑ w : Fin 3, l0 w * E0 0 w

def sV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := wmean (fun _ : Fin 20 => (1 : ℝ)) (fun u => μ0 - h u)
def HHV (μ0 μ2 : ℝ) (h : Fin 20 → ℝ) : ℝ := |sV μ0 h - μ2| + 1
def muMV (μ0 : ℝ) : ℝ := (μ0 - SgV + BeV) + 1 * Real.log (211 - 1) / (211 - 2)
def FoV : ℝ := UnitWeightPartition.Fo Finset.univ Finset.univ l0 F0
def LaV (μ0 μ1 : ℝ) (h : Fin 20 → ℝ) : ℝ := |muMV μ0| + |μ1 - SgV| + 2 * ∑ u, |h u|
def NcV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := |μ0| + ∑ u, |h u| + |FoV| + 1 + Real.log 211

def D1 (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Data Unit (fun _ => Fin 20) Unit 1 1 where
  x := HHV μ0 μ2 h
  ε := 0
  a := 1
  b := 1
  b' := 0
  k := 1
  L := Real.log 211
  La := LaV μ0 μ1 h
  B0 := |EeV|
  Nc := NcV μ0 h
  gam := 0
  LpL := 0
  v := Real.pi
  lg := 0
  logGam := 0
  aT := fun _ => 1
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 211
  muN := fun _ _ => μ0
  muMaxN := fun _ _ => μ1
  h := fun _ => h
  muM := fun _ _ => muMV μ0
  muMaxM := fun _ _ => μ1 - SgV
  EeJ := fun _ _ _ => EeV
  muCC := fun _ => μ0
  muMinCC := fun _ => μ2
  Fo := fun _ => FoV
  Ga := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  Ta := fun _ => UnitWeightPartition.Ta Finset.univ l0 tau0
  ASK := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  IO := fun _ => IOV
  HH := fun _ => HHV μ0 μ2 h
  del := fun _ => 0
  η := fun _ => 5 * (1 / 20) + 3 * Real.sqrt 0
  e := fun _ => 2 * 0
  delBar := 0
  etaBar := 1 / 4
  eBar := 0

def C2 : Consts := ⟨1, 1, 1, 1, 1, 1, 4, |IOV|, 1, 1⟩

end Model

namespace Model

theorem sum_abs_ge (h : Fin 20 → ℝ) (u : Fin 20) : |h u| ≤ ∑ u, |h u| :=
  Finset.single_le_sum (f := fun u => |h u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ u)

theorem sum_abs_nonneg (h : Fin 20 → ℝ) : 0 ≤ ∑ u, |h u| :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem LaV_nonneg (μ0 μ1 : ℝ) (h : Fin 20 → ℝ) : 0 ≤ LaV μ0 μ1 h := by
  have := sum_abs_nonneg h
  unfold LaV; positivity

theorem HHV_pos (μ0 μ2 : ℝ) (h : Fin 20 → ℝ) : 0 < HHV μ0 μ2 h := by
  unfold HHV; positivity

theorem setting (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) (hμ : μ0 ≤ μ1) : (D1 μ0 μ1 μ2 h).HidaSetting C2 := by
  refine ⟨HHV_pos μ0 μ2 h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => hμ, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [D1, C2, Real.pi_pos]

theorem div' (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).DIV C2 := by
  intro u0 u
  have h1 := le_abs_self μ0
  have h2 := (le_abs_self (h u)).trans (sum_abs_ge h u)
  have h3 := neg_abs_le FoV
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 := abs_nonneg EeV
  simp [D1, C2, Data.nT, Data.logOm, ph, Real.pi_ne_zero, NcV]
  linarith

theorem count (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Count5 (D1 μ0 μ1 μ2 h) C2 := by
  intro u0 u
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 : 0 ≤ Real.log 211 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [D1, C2, Real.pi_ne_zero]
    linarith
  · simp [D1, C2]
  · intro u'
    simp [D1, C2]

end Model

end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
