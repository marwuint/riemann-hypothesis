import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}

section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

end Global

end GlobalTheory.ShFam.Pad.BCEx
