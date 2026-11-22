import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.IoTop

theorem liftS_smul_domain {D : D7} {S T : HSp D} (om : Om S T) (ν μ : Measure (GA D T)) (c : ENNReal) (hc0 : c ≠ 0)
    (hμ : μ = c • ν) (hH : μ.IsHaarMeasure) {𝓕 𝓖 : Set (GA D T)} (h₁ : IsFundamentalDomain (GQ T) 𝓕 μ)
    (h₂ : IsFundamentalDomain (GQ T) 𝓖 ν) (G : GA D T → ℂ) (φ : WO S T → ℂ) (x : GA D S)
    (hinv : ∀ γ ∈ GQ T, ∀ y, om (x, γ * y) φ 0 * G (γ * y) = om (x, y) φ 0 * G y) :
    liftS om μ 𝓕 G φ x = (c.toReal : ℂ) • liftS om ν 𝓖 G φ x := by
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have h₂' : IsFundamentalDomain (GQ T) 𝓖 μ := h₂.mono (hμ ▸ Measure.smul_absolutelyContinuous)
  rw [liftS_apply, liftS_apply, h₁.setIntegral_eq h₂' fun γ y => hinv γ.1 γ.2 y, hμ, Measure.restrict_smul,
    integral_smul_measure, Complex.real_smul]
  rfl

theorem smul_const (a b : ℝ) (H z : ℂ) (hab : 0 ≤ a * b) :
    ((ENNReal.ofReal (a * b)).toReal : ℂ) • (H • z) = (H * (a : ℂ) * (b : ℂ)) • z := by
  rw [ENNReal.toReal_ofReal hab, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.Fam.IoTop

end
