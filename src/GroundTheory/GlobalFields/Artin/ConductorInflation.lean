import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal
import GroundTheory.LocalFields.DifferentGalois
import GroundTheory.LocalFields.ConductorTransport
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.LocalFields.ArtinConductorAbelian
import GroundTheory.LocalFields.BrauerInductionPrime
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.BrauerInductionClifford
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.LocalFields.LowerIndexQuotient
import GroundTheory.LocalFields.IntermediateField

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section GlobalInflation

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

section Tower

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

theorem completionMap_completionMap (a : v.adicCompletion K) :
    SemiLocal.completionMap u w (SemiLocal.completionMap v u a) =
      SemiLocal.completionMap v w a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((SemiLocal.continuous_completionMap u w).comp (SemiLocal.continuous_completionMap v u))
    (SemiLocal.continuous_completionMap v w) (funext fun x ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply, SemiLocal.completionMap_algebraMap]
    rw [IsScalarTower.algebraMap_apply K F (u.adicCompletion F),
      SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L),
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      ← IsScalarTower.algebraMap_apply K F L]

theorem isScalarTower_adicCompletion :
    IsScalarTower (v.adicCompletion K) (u.adicCompletion F) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (completionMap_completionMap v u w a).symm

attribute [local instance] isScalarTower_adicCompletion

variable [IsGalois K F] [IsGalois K L]

end Tower

variable [IsGalois K F] [IsGalois K L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalInflation

end GroundTheory.Global
