import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.Ix (D : Datum p) : Type := by
  letI := D.freeLa
  exact Module.Free.ChooseBasisIndex ℤ D.La

instance (D : Datum p) : Fintype D.Ix := by
  letI := D.freeLa
  letI := D.finLa
  unfold Datum.Ix
  infer_instance

instance (D : Datum p) : DecidableEq D.Ix := Classical.decEq _

def Datum.basis (D : Datum p) : Module.Basis D.Ix ℤ D.La := by
  letI := D.freeLa
  exact Module.Free.chooseBasis ℤ D.La

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT

namespace GlobalTheory.DrinLev.HT

end GlobalTheory.DrinLev.HT

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
