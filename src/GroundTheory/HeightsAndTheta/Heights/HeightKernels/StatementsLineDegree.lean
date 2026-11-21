import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

abbrev ProjIdx (K : Type) [Field K] [NumberField K] (i : ℕ) : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin i

abbrev projBlocks (K : Type) [Field K] [NumberField K] (i : ℕ) : Unit → Type := fun _ => ProjIdx K i

abbrev ProjField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin i) K)

open scoped Classical in

def embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (z : ProjIdx K i → ℂ) :
    Fin i → ℂ :=
  fun j => ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single σ 1) m * z (m, j)

def LineOfLargeDegreeFromZ.Statement : Prop :=
  SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → LineOfLargeDegree.Statement

end

end GroundTheory.Heights₂.Heights
