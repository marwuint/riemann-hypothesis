import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive

namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := _root_.GlobalTheory.BinaryRep.represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
