import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdmissibleOfIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKfin

noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate ContDiff Topology

namespace GlobalTheory.CompanionTheory.GelfAct

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have h : ∀ t : ℝ, (t : ℂ) • X = t • X := fun t => by ext; simp
  simp only [h]
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end GlobalTheory.CompanionTheory.GelfAct

end
