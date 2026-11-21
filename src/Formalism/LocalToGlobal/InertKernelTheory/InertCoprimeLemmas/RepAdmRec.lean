import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp
open scoped TensorProduct

namespace Formalism.L2.KerInert.RepRec

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

end Gen

end Formalism.L2.KerInert.RepRec
