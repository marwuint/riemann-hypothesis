import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1

open Classical in

def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0

end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFvL (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvL (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

end Glob

end GlobalTheory.StdPairCone
