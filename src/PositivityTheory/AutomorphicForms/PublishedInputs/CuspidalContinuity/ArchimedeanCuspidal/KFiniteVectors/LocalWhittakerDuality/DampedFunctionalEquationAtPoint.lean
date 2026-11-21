import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def hI (p : Fˣ × Fˣ × GL (Fin 2) F) : GL (Fin 2) F := dg2 (p.1 * p.2.1) p.2.1 * p.2.2

end D

end Ad3.K.GL2LocalData
