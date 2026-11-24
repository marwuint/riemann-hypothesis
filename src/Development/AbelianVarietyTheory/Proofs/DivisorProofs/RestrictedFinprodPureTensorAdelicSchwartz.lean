module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RestPure

theorem evFin_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) :
    evFin F v (z i) = 0 := by

  have hu : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  have h := congrFun (hz _ hu) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 := congrArg (evFin F v) h
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem rest_evI_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  intro F _ _ κ _ φ hφ hcof f
  refine ⟨fun x z hz => ?_, ?_⟩
  ·
    have hc : ∀ v i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
      rw [Pi.add_apply, map_add (f := _), evFin_eq_zero z hz v i, add_zero]
    simp only [hc]
  ·
    have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        SB (κ → FiniteAdeleRing (𝓞 F) F) :=
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩
    exact Submodule.subset_span ⟨f, _, hg, rfl⟩

end GlobalTheory.RestPure
