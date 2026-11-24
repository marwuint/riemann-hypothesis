module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.uiLaws :
    UILaws := by
  intro E _ _ β hc hinv
  have hf : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) :=
    hc.comp continuous_subtype_val
  have hcl := isCompact_closure_normOneFundamentalDomain E
  have hinv' : ∀ (k : Eˣ) (u : IdeleGroup.normOneSubgroup E),
      β ((u * diagonalToNormOne E k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (u : IdeleGroup E) := by
    intro k u
    have h := hinv k (u : IdeleGroup E)
    rwa [mul_comm] at h
  refine ⟨?_, ?_, ?_⟩
  · exact (hf.continuousOn.integrableOn_compact hcl).mono_set subset_closure
  · obtain ⟨B, hB⟩ := hcl.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨B, fun t ht => ?_⟩
    have hm : t ∈ IdeleGroup.normOneSubgroup E := MonoidHom.mem_ker.2 (Subtype.ext ht)
    obtain ⟨k, hk, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E ⟨t, hm⟩
    have h := hB _ (subset_closure hk)
    rwa [hinv' k ⟨t, hm⟩] at h
  · intro d hd
    have hm : d ∈ IdeleGroup.normOneSubgroup E := MonoidHom.mem_ker.2 (Subtype.ext hd)
    set b : IdeleGroup.normOneSubgroup E := ⟨d, hm⟩ with hb
    set g : IdeleGroup.normOneSubgroup E → ℂ := fun z => β (z : IdeleGroup E) with hg
    have hD := isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)
    have hD' := hD.smul_of_comm b
    have hI : ∀ (γ : (diagonalNormOne E).op) (x : IdeleGroup.normOneSubgroup E), g (γ • x) = g x := by
      rintro ⟨γ, hγ⟩ x
      obtain ⟨k, hk⟩ := Subgroup.mem_op.1 hγ
      have e : γ.unop = diagonalToNormOne E k := Subtype.ext hk.symm
      change g (x * γ.unop) = g x
      rw [e]
      exact hinv' k x
    have h1 := hD.setIntegral_eq hD' hI
    have h2 := (measurePreserving_mul_left (normOneMeasure E) b).setIntegral_image_emb
      (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain E)
    unfold UI
    change ∫ z in normOneFundamentalDomain E, g (z * b) ∂normOneMeasure E = ∫ z in normOneFundamentalDomain E, g z ∂normOneMeasure E
    rw [h1]
    simp_rw [mul_comm _ b]
    exact h2.symm
