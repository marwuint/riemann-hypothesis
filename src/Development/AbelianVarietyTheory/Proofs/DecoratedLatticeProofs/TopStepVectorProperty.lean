import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChain

theorem multT_apply_continuous {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    Continuous (u v) := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 : Continuous (u (PiTensorProduct.tprod ℂ f)) := (GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f).2.1
    rw [map_smul]
    exact h2.const_smul r
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

theorem multT_apply_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    ∀ γ ∈ GQ V, ∀ h, u v (γ * h) = u v h := by
  intro γ hγ h
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 : u (PiTensorProduct.tprod ℂ f) (γ * h) = u (PiTensorProduct.tprod ℂ f) h :=
      (GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f).1 γ hγ h
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, h2]
  | add x y hx hy =>
    rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]

theorem weil_transport {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

end GlobalTheory.BaseChain
