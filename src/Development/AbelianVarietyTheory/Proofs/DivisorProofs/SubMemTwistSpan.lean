import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

end GlobalTheory.RankCoinv
