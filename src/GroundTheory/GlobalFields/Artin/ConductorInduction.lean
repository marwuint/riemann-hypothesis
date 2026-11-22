import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.PlacesGalois
import GroundTheory.GlobalFields.Artin.Mackey
import GroundTheory.GlobalFields.Artin.Places
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.Different
import GroundTheory.GlobalFields.Artin.PlacesFrobenius
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite

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
