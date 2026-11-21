import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top Filter Topology

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

structure GenModel (R : RootModel Ψ N) (Λ : ℝ) where

  F : Type
  [fieldF : Field F]
  [nfF : NumberField F]
  [algF : Algebra F R.Ω]

  I : Type
  [finI : Fintype I]

  w : I → R.Ω

  L : HermLine (fun _ : Unit => I)
  L_deg : L.a = fun _ => 1
  arith : IsArithVar (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) (dimFl Ψ N + 1)
  gen : IsGenH (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) L Λ
  deg_pos : 0 < geomDeg (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) L (dimFl Ψ N)

attribute [instance] GenModel.fieldF GenModel.nfF GenModel.algF GenModel.finI

namespace GenModel

end GenModel

end GlobalTheory.CompanionTheory.Ar.Small
