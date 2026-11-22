import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
namespace ResidueCardinalityNilpotence
namespace GlobalTheory.CompanionTheory.ResCardPlace
end GlobalTheory.CompanionTheory.ResCardPlace
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
noncomputable section
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.L2.DIV
theorem finCoefK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  have hL := s.core.lev
  have hde := Test.pde_ne_q s
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : 1 ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    omega
  refine ⟨dlF ch.G, loss_dlF ch.G hC hb hf, fun t w hA Φ β hβ => ?_⟩
  have hq := coef_QL hL ch.S.toGridChoice t Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard t) hA hβ
  refine ⟨((∏ v, (ch.S.term t Φ β v).coef : ℚ) : D.what₂.LL), ?_, ?_⟩
  · rw [map_ratCast]
    push_cast
    rfl
  · rcases hq with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h
end GlobalTheory.CompanionTheory.VolVal
end
end
end ResidueCardinalityNilpotence
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt
end
end
