import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

theorem isModelU_iff {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : IsModelU lam Λ C ↔ GL3Theta.IsModelU lam Λ C := Iff.rfl

theorem at_iff (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) :
    At D cc δ g ↔ GL3Theta.At D cc δ ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩ := Iff.rfl

theorem at_iff' (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) :
    GL3Theta.At D cc δ g ↔ At D cc δ ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩ := Iff.rfl

end GlobalTheory.Glob.IntegralWittCoefficients
