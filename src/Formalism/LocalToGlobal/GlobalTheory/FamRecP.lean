import Formalism.LocalToGlobal.GlobalTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

theorem ell_plF (D : D7) (w : D.what₂.places.Pl) : slopeLatticeData.ell (plF D w) = SizeData₂.lwP w := rfl

variable {D : D7} (L : SizeData₂ D)

section Proj
variable (m : ℕ) (A : Mx D)

theorem lenR_famOf (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).lenR u z = (fam0 L m A).lenR u z := rfl

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

namespace FieldEq

end FieldEq

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

