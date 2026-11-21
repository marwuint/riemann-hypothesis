import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP.IoLevPf

theorem multT_val {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    (∀ γ ∈ GQ V, ∀ g, u v (γ * g) = u v g) ∧ ∀ k ∈ J, ∀ g, u v (g * k) = χ k * u v g := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f
    have h3 : ∀ g, u (PiTensorProduct.tprod ℂ f) g = (PiTensorProduct.lift.symm u) f g := fun g => by simp
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.1 γ hγ g]
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.2.2 k hk g, smul_eq_mul, smul_eq_mul]
      ring
  | add x y hx hy =>
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.2 k hk g, hy.2 k hk g]
      ring

end GlobalTheory.StepLevelP.IoLevPf

namespace GlobalTheory.StepLevelP

end GlobalTheory.StepLevelP

end
