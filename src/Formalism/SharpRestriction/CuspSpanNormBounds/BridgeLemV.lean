import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.BridgeLemV

open NumberField Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem std_form_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdForm K n = stdForm K n := rfl

theorem std_lattice_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdLat K n = stdLat K n := rfl

end Formalism.MainNotions.BridgeLemV

end
