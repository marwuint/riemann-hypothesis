import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.IntertwiningIsomorphisms.IsoIffIntertwiningHolds

noncomputable section

open Polynomial CategoryTheory

namespace Formalism.L2.PT

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.RT Formalism.IrreducibleCountingLemmas.TYPES

section Conv

variable {D : D7} {jE : D.host.E →+* Formalism.L2.Host.Qb}

def convOf (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabelConv (ZMod (D.host.g k)) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.L2.NT.convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (T.ζ k) (T.ζ_gen k)

theorem convOf_ι (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (convOf T k).ι = D.ntypes.teichC k := rfl

theorem convOf_gen (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (convOf T k).gen = T.ζ k := rfl

end Conv

end Formalism.L2.PT

end

namespace Formalism.L2.PT
end Formalism.L2.PT
