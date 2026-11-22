import Formalism.LocalToGlobal.GlobalTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D)

section Proj
variable (m : ℕ) (A : Mx D)

end Proj

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.HN.DualPolygon

namespace Len

section NF

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem lenAt_eq (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V) :
    slopeLatticeData.lenAt w A B = (have := w.2.isPrime; slopeLatticeData.locLen w.1 (A ⧸ B.comap A.subtype)) := rfl

end NF

end Len

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec

namespace Formalism.L2.GlobalTheoryTheory.FamRec

end Formalism.L2.GlobalTheoryTheory.FamRec
