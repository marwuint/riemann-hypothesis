import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.AdelicCharDilate

theorem exists_eq_std_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  intro F E _ _ _ _ _ _ σ hCM _ _ ψ₀ h₀ ψ h
  haveI := hCM.1
  exact _root_.GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 h

end GlobalTheory.AdelicCharDilate
