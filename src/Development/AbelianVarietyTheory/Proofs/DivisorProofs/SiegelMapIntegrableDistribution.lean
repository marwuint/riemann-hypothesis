import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinMApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemSB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

end GlobalTheory
