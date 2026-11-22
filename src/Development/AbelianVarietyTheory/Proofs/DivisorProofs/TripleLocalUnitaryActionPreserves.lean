import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance mA : MeasurableSpace (κ → AF F) := borel _
local instance bA : BorelSpace (κ → AF F) := ⟨rfl⟩
local instance mV (v : Pl F) : MeasurableSpace (κ → Fv F v) := borel _
local instance bV (v : Pl F) : BorelSpace (κ → Fv F v) := ⟨rfl⟩

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance mA' : MeasurableSpace (κ → AF F) := borel _
local instance bA' : BorelSpace (κ → AF F) := ⟨rfl⟩
local instance mV' (v : Pl F) : MeasurableSpace (κ → Fv F v) := borel _
local instance bV' (v : Pl F) : BorelSpace (κ → Fv F v) := ⟨rfl⟩

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

end GlobalTheory.LocalUnitaryL2

