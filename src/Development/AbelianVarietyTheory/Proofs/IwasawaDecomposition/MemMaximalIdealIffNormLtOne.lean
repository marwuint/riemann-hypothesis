module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntMaxFinExt

theorem mem_maximalIdeal_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  intro l _ K _ y
  have hle : ∀ z : ↥(Loc.OL K), ‖((z : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := fun z =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (z : ↥K.1)).1 z.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hlt
    have h1 : ‖((y : ↥K.1) : PadicAlgCl l)‖ = 1 := le_antisymm (hle y) (not_lt.1 hlt)
    have hy0 : (y : ↥K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have hinv : ((y : ↥K.1)⁻¹ : ↥K.1) ∈ Loc.OL K := by
      rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
      rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
    apply hnu
    refine ⟨⟨y, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hy0)
    · exact Subtype.ext (inv_mul_cancel₀ hy0)
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    have hm : ((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l)) * ((((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l) = 1 := by
      have := congrArg (fun z : ↥(Loc.OL K) => (((z : ↥K.1)) : PadicAlgCl l)) u.mul_inv
      exact this
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    have h2 := hle ((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K))
    have h0 : 0 ≤ ‖((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l))‖ := norm_nonneg _
    nlinarith

end GlobalTheory.IntMaxFinExt
