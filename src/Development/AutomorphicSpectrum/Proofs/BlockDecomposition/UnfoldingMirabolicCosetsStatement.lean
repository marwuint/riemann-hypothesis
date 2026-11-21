import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.RSUnfold

instance countableGL : Countable (GL (Fin 2) ℚ) :=
  have : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u : Matrix (Fin 2) (Fin 2) ℚ)) Units.val_injective

instance secondCountable_adelic_GL2 : SecondCountableTopology G2 := by
  have h2 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) 𝔸[ℚ])).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end GlobalTheory.CompanionTheory.RSUnfold

end
