import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponentialOfSemiAbelianFibre_linearChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (M : Matrix (Fin g) (Fin g) ℂ), IsUnit M.det → IsHolTo Set.univ (fun z => (e z).left) → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y e → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y (fun w => e (M *ᵥ w)) := by
  exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec
