import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def detA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* AE F E :=
  Matrix.detMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem detA_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) : detA J g = (mat g).det := rfl

theorem arch_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (τ : EmbOver E w) (g : GAd σ J) (i j : Fin n) :
    GlobalTheory.Orb.archMat σ J τ (projArch σ J w g) i j = piInf τ (g.1.1 i j) := rfl

end GlobalTheory.Published.LeviCentreModel

end
