import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnitsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuantumDeterminantEigenvalue
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsUnitary

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem isMod_smooth_of_isDS : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  intro hH k r ε mu R hk hDS Q E hQ hE
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hU : IsUnit Q := by
    have h1 : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ.2
    have h2 : star Q * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    exact ⟨⟨Q, star Q, h1, h2⟩, rfl⟩
  have hG : Formalism.REAL.GlRel E := (GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hDS Q E hU hE).1
  refine ⟨hG, _root_.Gp91.GlobalTheory.CapUnitary.isUnitary_of_isE hK k r ε mu R hDS Q E hQ hE, ?_⟩
  exact _root_.GlobalTheory.CapelliCasimir.cas_of_capelli R.smSub (2 * r + k + 1) E mu (by omega) hG
    (_root_.Gp91.GlobalTheory.CapelliSmooth.qdet_smooth hH k r ε mu R hDS Q E hU hE)

end GlobalTheory
