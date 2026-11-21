import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingFactorStage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

theorem gBig_of₃ {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqTower

end
