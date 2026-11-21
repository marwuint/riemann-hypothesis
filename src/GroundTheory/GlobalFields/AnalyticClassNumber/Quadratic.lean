import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.Artin.Series
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.Artin.InductionLocal
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.LocalFields.BrauerInductionPrime
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.LocalFields.BrauerInductionClifford
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
import GroundTheory.GlobalFields.Artin.Regular
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
import GroundTheory.LocalFields.DifferentGalois

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology Complex NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

namespace Quadratic

section Two

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_ne_one_of_card_eq_two (hG : Nat.card G = 2) {σ τ : G} (hσ : σ ≠ 1) (hτ : τ ≠ 1) :
    σ = τ := by
  classical
  have := Fintype.ofFinite G
  by_contra h
  have hcard : ({1, σ, τ} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h]
    simp [Ne.symm hσ, Ne.symm hτ]
  have hle := Finset.card_le_univ ({1, σ, τ} : Finset G)
  rw [hcard, Fintype.card_eq_nat_card, hG] at hle
  omega

omit [Finite G] in

theorem mul_self_eq_one_of_card_eq_two (hG : Nat.card G = 2) (σ : G) : σ * σ = 1 := by
  have h := pow_card_eq_one' (G := G) (x := σ)
  rwa [hG, pow_two] at h

theorem exists_ne_one_of_card_eq_two (hG : Nat.card G = 2) : ∃ σ : G, σ ≠ 1 := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  exact exists_ne 1

open Classical in

def signChar (hG : Nat.card G = 2) : G →* ℂˣ where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' σ τ := by
    by_cases hσ : σ = 1
    · subst hσ
      simp
    by_cases hτ : τ = 1
    · subst hτ
      simp
    obtain rfl := eq_of_ne_one_of_card_eq_two hG hσ hτ
    simp [mul_self_eq_one_of_card_eq_two hG, hσ]

end Two

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem card_gal : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

def galChar : Gal(K/ℚ) →* ℂˣ :=
  signChar (card_gal K)

def heckeChar : HeckeCharacter ℚ :=
  heckeCharacterOfChar (galChar K)

theorem isOfFinOrder_heckeChar : IsOfFinOrder (heckeChar K) :=
  isOfFinOrder_heckeCharacterOfChar _

def kroneckerData : DirichletHecke.PrimitiveDirichletCharacter :=
  DirichletHecke.finiteOrderEquiv.symm ⟨heckeChar K, isOfFinOrder_heckeChar K⟩

def level : ℕ :=
  ((kroneckerData K).1 : ℕ)

instance : NeZero (level K) :=
  ⟨(kroneckerData K).1.ne_zero⟩

end Quadratic

end GroundTheory.Global
