import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveEtaleLocallyHasSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace GlobalTheory.EtC

theorem chains_cechAug_quasiIso_of_smooth (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)
    [Smooth f] [Surjective f] : QuasiIso ((chains R).map (cechAug f)) :=
  GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R (yoneda.map f) (fun U y => _root_.GlobalTheory.EtC.smooth_surjective_loc_sections f U y)

end GlobalTheory.EtC
