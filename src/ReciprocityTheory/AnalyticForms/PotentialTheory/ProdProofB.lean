import ReciprocityTheory.AnalyticForms.PotentialTheory.ProdProofA
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M

open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

instance openAtlas_subsingleton {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    Subsingleton (Fin (openAtlas U hU hne).n) :=
  inferInstanceAs (Subsingleton (Fin 1))

end

end ReciprocityTheory.AnForm.M
