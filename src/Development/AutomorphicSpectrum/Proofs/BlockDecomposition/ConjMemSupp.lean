import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.StrongApproxSub

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

abbrev mt (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mt_mul (g h : HA (AF F) σ J) : mt (g * h) = mt g * mt h := rfl

theorem mt_one : mt (1 : HA (AF F) σ J) = 1 := rfl

end Group

end GlobalTheory.CompanionTheory.StrongApproxSub

end
