import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartCone

theorem isCN_chartRing (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] : IsCN (ChartRing k m e) := by
  have : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
  refine ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2, ?_, inferInstance⟩
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  exact GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

end GlobalTheory.ChartCone
