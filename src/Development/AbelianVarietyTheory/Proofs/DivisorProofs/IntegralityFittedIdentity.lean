import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie

