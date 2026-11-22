import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriods
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add, LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo

end
