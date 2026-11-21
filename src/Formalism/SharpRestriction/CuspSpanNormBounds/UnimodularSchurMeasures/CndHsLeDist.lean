import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cnd_V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n × Fin n)

def cnd_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : cnd_V n := WithLp.toLp 2 fun p => M p.1 p.2

theorem cnd_vec_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : cnd_vec M - cnd_vec N = cnd_vec (M - N) := rfl

end Formalism.MainNotions.LeviCoordinates

end
