import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.MixModel GlobalTheory.Grow
open scoped TensorProduct NNReal ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

variable {D : D7}

abbrev Letter (D : D7) (m n : ℕ) : Type := D.what₂.Tau × Fin m × Fin n × Bool

def Letter.mat {m n : ℕ} (a : Letter D m n) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)

end GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

end
