import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := _root_.GlobalTheory.RegSch.good_level_conj_stab D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
