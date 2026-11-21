import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ShortRuleRepresentationChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortSpanCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism hiding IsShortRule shortGen ShortInCusp
open GlobalTheory.GenusLatCompare GlobalTheory.LevelCoverCompare GlobalTheory.TransferCompare

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Generators

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem evR_of_frMap {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf : f ∈ sec Xo c a n) {p : TRing c.F}
    {S : Type} [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) {y : FrPt Xo c p.R} {z : FrPt Xo c S}
    (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact evalWD_framed Xo c f hf.1 S _ _ _ _ _ _ z hT.choose_spec.choose_spec.choose_spec h

variable {Δ}

end Generators

end GlobalTheory.ShortSpanCompare
