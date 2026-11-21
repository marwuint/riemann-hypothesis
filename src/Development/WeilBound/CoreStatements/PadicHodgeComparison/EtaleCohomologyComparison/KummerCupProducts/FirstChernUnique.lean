import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.Inputs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.E

theorem etMap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtMap l K :=
  Main.etale_comparison_map etIn l (CrystallineSemistableComparison.R.forE l) K

end CrystallineSemistableComparison.E
