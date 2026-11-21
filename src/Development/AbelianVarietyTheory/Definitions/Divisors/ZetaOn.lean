import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ThK.Bot

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

structure IsDbl (B : Base F E) (X : Spc F E n) (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J)
    (K₂ : Subgroup (UA σ X₂.J)) : Prop where
  gram : X₂.J = dblGram finSumFinEquiv X.J
  lat : X₂.L = sumLat finSumFinEquiv X.L X.L
  maj : ∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)
  emb : ∀ g g', mat (i (g, g')) = blkMat finSumFinEquiv (mat g) (mat g')
  stab : IsStab B K₂
  iwa : IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂

end GlobalTheory.ThK.Bot

end
