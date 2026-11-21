import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  first | (exact @GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (exact GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (intros; apply GlobalTheory.KOneTransport.fixed_ne_bot_transport  <;> assumption)
