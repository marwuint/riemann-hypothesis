import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagExpZero

open GlobalTheory.FrameTwistCompare (lin quad)
open MvPowerSeries (constantCoeff pderiv)

section Flat

variable {S : Type} [CommRing S] {σ : Type}

def Flat (f : MvPowerSeries σ S) : Prop := constantCoeff f = 1 ∧ ∀ v, lin v f = 0

theorem flat_one : Flat (1 : MvPowerSeries σ S) := ⟨map_one _, fun v => by simp [lin]⟩

theorem quad_one (v w : σ) : quad v w (1 : MvPowerSeries σ S) = 0 := by simp [quad]

theorem Flat.mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) : Flat (f * g) := by
  refine ⟨by rw [map_mul, hf.1, hg.1, _root_.mul_one], fun v => ?_⟩
  have h1 := hf.2 v
  have h2 := hg.2 v
  unfold lin at h1 h2 ⊢
  simp [Derivation.leibniz, h1, h2]

theorem Flat.quad_mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) (v w : σ) :
    quad v w (f * g) = quad v w f + quad v w g := by
  have h1 := hf.2 v
  have h2 := hg.2 v
  have h3 := hf.2 w
  have h4 := hg.2 w
  unfold lin at h1 h2 h3 h4
  simp [quad, Derivation.leibniz, h1, h2, h3, h4, hf.1, hg.1, add_comm]

theorem Flat.pow {f : MvPowerSeries σ S} (hf : Flat f) (q : ℕ) :
    Flat (f ^ q) ∧ ∀ v w, quad v w (f ^ q) = q * quad v w f := by
  induction q with
  | zero => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | succ q ih =>
    refine ⟨by rw [pow_succ]; exact ih.1.mul hf, fun v w => ?_⟩
    rw [pow_succ, ih.1.quad_mul hf, ih.2]
    push_cast
    ring

end Flat

end GlobalTheory.DiagExpZero
