import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

open GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitRow.IdxV

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (c : k) : AddSubgroup k := (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulRight c)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_ball (c x : k) : x ∈ ball c ↔ x * c ∈ 𝒪[k] := Iff.rfl

variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]

end GlobalTheory.CompanionTheory.SplitRow.IdxV
