import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.PlacesGalois

set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module IntermediateField

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalTower

variable {K F L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [ValuativeExtension K F] [ValuativeExtension F L] [ValuativeExtension K L]
  [FiniteDimensional K F] [FiniteDimensional F L] [FiniteDimensional K L] [IsGalois K L]

end LocalTower

end GroundTheory.Global
