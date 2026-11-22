import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

namespace GlobalTheory.LettersCheck

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem isInfEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

end GlobalTheory.LettersCheck
