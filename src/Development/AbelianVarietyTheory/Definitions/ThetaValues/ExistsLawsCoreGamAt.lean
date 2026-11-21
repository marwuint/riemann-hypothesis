import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

noncomputable section

namespace GlobalTheory.RunIn.Check

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

theorem gamAt_iff (T : Core D) : GamAt T ↔ ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    GlobalTheory.FrameNorm.HasPrinc (⟨(T.U j σ).Comp, (T.U j σ).X, (T.U j σ).un⟩ : Formalism.L2.PjFree.Unf _ _ σ _) T.Q.l.M :=
  Iff.rfl

end GlobalTheory.RunIn.Check
