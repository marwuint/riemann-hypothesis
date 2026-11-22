import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have h1 : (d.pX ⬝ d.jX) i i = 1 := by rw [d.pX_jX]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
