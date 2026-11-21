import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Formalism.LocalToGlobal.IndefiniteReal.TopMult

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

end GlobalTheory.RegSch.CentreRight

end
