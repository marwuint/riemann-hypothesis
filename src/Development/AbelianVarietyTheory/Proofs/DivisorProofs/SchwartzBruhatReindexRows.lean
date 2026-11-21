import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

def glRenum (e : A ≃ A') : GL A' k →* GL A k :=
  Units.map (Matrix.reindexAlgEquiv k k e.symm).toMonoidHom

theorem glRenum_val (e : A ≃ A') (g : GL A' k) : (glRenum e g).val = g.val.submatrix e e := rfl

end GlobalTheory.RankStrata
