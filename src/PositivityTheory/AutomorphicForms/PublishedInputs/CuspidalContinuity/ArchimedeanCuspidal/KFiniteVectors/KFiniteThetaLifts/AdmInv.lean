import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable {K : Type} [Field K] [NumberField K]

structure Pk (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)) (I Z Id Zd : ℂ → ℂ) : Prop where
  dI : Differentiable ℂ I
  oI : Ord I (1 / 3)
  eu : ∀ s : ℂ, 1 < s.re → I s = Z s * eulK DK c S s
  nZ : ∀ s : ℂ, 1 / 4 < s.re → Z s ≠ 0
  dZ : DifferentiableOn ℂ (fun s => (Z s)⁻¹) {s | 1 / 4 < s.re}
  oZ : Ord (fun s => (Z s)⁻¹) (1 / 3)
  dId : DifferentiableOn ℂ Id {s | 1 / 4 < s.re}
  dZd : DifferentiableOn ℂ Zd {s | 1 / 4 < s.re}
  eud : ∀ s : ℂ, 1 < s.re → Id s = Zd s * eulK DK c⁻¹ S s
  fe : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → I s = Id (1 - s)
  lfe : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → Zd (1 - s) = gamSK DK c n t S s * Z s

end Ad3.K.QuadraticBaseChangeGL3
