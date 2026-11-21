import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.JsR

def LocalExpBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π →
    ∃ (h : ℕ) (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd))

end PositivityTheory.JsR

end
