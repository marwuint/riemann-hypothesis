import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

theorem itLine_of_discreteSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  intro hCover hModules D

  rcases _root_.GlobalTheory.RealPlaceTheta.exists_record_theta hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩

  have hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hCover hModules D
  have hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := _root_.GlobalTheory.VacuumCharacter.vacChar D
  exact itLine D X hParam hAR3 hVac hBridge hModules

end GlobalTheory.Chain.RealLine
