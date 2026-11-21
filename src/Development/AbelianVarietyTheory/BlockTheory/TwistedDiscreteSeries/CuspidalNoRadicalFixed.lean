import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult
open GlobalTheory.Orb (TypeDataG CcGA ResF)
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev radicalTwo (k : Type) [CommRing k] {a b r : ℕ} (h : a + b = r) : Subgroup (GL (Fin r) k) :=
  GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def NoRadicalFixed {V : HSp D} (T : TypeDataG V) : Prop :=
  ∀ (a b : ℕ) (h : a + b = V.rank), 0 < a → 0 < b → ∃ v : T.S, fixed (T.τ v) (radicalTwo (ResF v.1) h) = ⊥

def RadicalIntegralsVanish (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ 𝔉 : IsoFlag V, 𝔉.Proper → ∀ ν : Measure (NA 𝔉), ν.IsHaarMeasure →
    ∀ x y : GA D V, ∫ n : NA 𝔉, f (x * (n : GA D V) * y) ∂ν = 0

variable (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

structure IsCuspidalOp (f : GA D V → ℂ) : Prop where

  map_mem : ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

  map_orthogonal : ∀ F ∈ (L2cusp V μ)ᗮ, RopG V μ f F = 0

  traceClass : IsTraceClass (RopG V μ f)

  integrable_kernel : ∀ (F : DividedPowerChartLift V μ) (p : Quot (GQ V)),
    Integrable (fun q => kernelQ (GQ V) f p q * F q) (autMeasure V μ)

  apply_eq_kernel : ∀ F : DividedPowerChartLift V μ,
    RopG V μ f F =ᵐ[autMeasure V μ] fun p => ∫ q, kernelQ (GQ V) f p q * F q ∂autMeasure V μ

  integrable_diag : Integrable (fun p => kernelQ (GQ V) f p p) (autMeasure V μ)

  trace_eq_integral : trace (RopG V μ f) = ∫ p, kernelQ (GQ V) f p p ∂autMeasure V μ

  mult_finite : ∀ c : UDual (GA D V), mCusp V μ c.rep.π < Cardinal.aleph0

  traceClass_rep : ∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)

  summable_norm : Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖

  hasSum_trace : HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f)
    (trace (RopG V μ f))

def CuspidalOperators : Prop :=
  ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → RadicalIntegralsVanish V (starFn f) → IsCuspidalOp V μ f

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

end
