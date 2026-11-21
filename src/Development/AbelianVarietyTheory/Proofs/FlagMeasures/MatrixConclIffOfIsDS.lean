import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SchurProjCompare

section Abstract

variable {G : Type} [Group G]
variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCyclic (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) : Prop :=
  Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set Hs)

omit [Group G] in

theorem IsCyclic.ext {σ : G → (Hs →L[ℂ] Hs)} {w : Hs} (h : IsCyclic σ w) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {A B : Hs →L[ℂ] E}
    (hAB : ∀ g, A (σ g w) = B (σ g w)) : A = B :=
  ContinuousLinearMap.ext_on h (by rintro _ ⟨g, rfl⟩; exact hAB g)

end Abstract

end GlobalTheory.SchurProjCompare
