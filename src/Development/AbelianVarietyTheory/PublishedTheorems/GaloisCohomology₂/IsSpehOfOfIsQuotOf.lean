import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ByClassModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

variable (E N) in

def Clauses : Prop :=
  (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        GlobalTheory.UnitaryBC.IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V →
        V ≤ ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a) (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) ∧
    (∀ V V' : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → GlobalTheory.UnitaryBC.IsDiscrete V' →
      ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.DiscSpec.ByClassModel

end
