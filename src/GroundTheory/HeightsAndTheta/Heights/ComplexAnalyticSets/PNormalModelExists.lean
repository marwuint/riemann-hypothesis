import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonemptyNormalModelOfPresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

theorem nonempty_normalModel_of_presentation {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker

theorem NormalModelExists.proof : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
