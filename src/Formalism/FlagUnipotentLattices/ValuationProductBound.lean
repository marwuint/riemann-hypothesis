import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

namespace Formalism.HermitianLatticeCounting.Final.S4

theorem weightedCS : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.S4aux.weighted_cauchy_schwarz
theorem omCount : Formalism.HermitianLatticeCounting.S4.OmCount := Formalism.HermitianLatticeCounting.P.S4aux.orbit_count_formula
theorem step4 : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.S4aux.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.Final.S4
