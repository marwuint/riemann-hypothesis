import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

noncomputable section

open NumberField Formalism.REAL

namespace UpperTheory.V.Lit

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def res (π : TR.CuspSub E a) (w : InfinitePlace E) (i j : Fin a) : Module.End ℂ π.V :=
  (TR.Eop w i j).restrict (π.stable (.lie _))

end UpperTheory.V.Lit
