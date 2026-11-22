import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

noncomputable section

namespace GlobalTheory.ThetaFac

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

structure WStable (B : Base F E) (om : Rep σ Y W) (D N : Submodule ℂ (Fn F n d)) : Prop where
  fin : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N
  lie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ D,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

end GlobalTheory.ThetaFac

end

namespace GlobalTheory.ThetaFac

end GlobalTheory.ThetaFac
