import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end
