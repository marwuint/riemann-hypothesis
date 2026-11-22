import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarRationalTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaEx

theorem selfDualLattice_intertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : UnitAt q a)
    (hub : UnitAt q b) : UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dif_pos hab, dif_pos ha', dif_pos hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.MovedKappaEx

namespace GlobalTheory.MovedKappaEx

end GlobalTheory.MovedKappaEx
