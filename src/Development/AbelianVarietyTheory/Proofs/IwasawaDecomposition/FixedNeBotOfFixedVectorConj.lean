import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplitData

theorem fixed_ne_bot_of_fixed_vector_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ h hloc f hf hf0 hfix
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf L n) (g : Formalism.AUTREP.GAf L n → ℂ), NG.rt L n (a * b) g = NG.rt L n a (NG.rt L n b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf L n → ℂ, NG.rt L n 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf L n, TrivOutside {s.v} a → TrivOutside {s.v} b → TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine GlobalTheory.FixedAtSplit.fixed_ne_bot_of_fixed_vector L n π s τ hloc (NG.rt L n x⁻¹ f) ?_ ?_ ?_
  · exact π.stable _ f hf
  · intro h0
    apply hf0
    rw [← hone f, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hfix (x * κ * x⁻¹) (hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx)) (by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc n κ * h⁻¹) * h = s.loc n κ by group]
      exact hk)
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]

end GlobalTheory.RowLevelSplitData

end
