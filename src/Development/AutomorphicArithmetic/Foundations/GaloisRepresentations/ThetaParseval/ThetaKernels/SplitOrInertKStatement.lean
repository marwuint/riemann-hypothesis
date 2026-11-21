import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertK

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
theorem _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @_root_.GlobalTheory.KFinLoc.split_or_inert_k | exact _root_.GlobalTheory.KFinLoc.split_or_inert_k | (intros; apply _root_.GlobalTheory.KFinLoc.split_or_inert_k <;> assumption)
end
