import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

instance (P : ArithVariety n) : P.ideal.IsPrime := P.isPrime

abbrev CoordRing (P : ArithVariety n) : Type := MvPolynomial (Coord n) ℤ ⧸ P.ideal

def FunField (P : ArithVariety n) : Type := FractionRing (CoordRing P)

instance (P : ArithVariety n) : Field (FunField P) := inferInstanceAs (Field (FractionRing _))

instance (P : ArithVariety n) : Algebra (CoordRing P) (FunField P) :=
  inferInstanceAs (Algebra _ (FractionRing _))

instance (P : ArithVariety n) : IsFractionRing (CoordRing P) (FunField P) :=
  inferInstanceAs (IsFractionRing _ (FractionRing _))

def val (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) : FunField P :=
  algebraMap (CoordRing P) (FunField P) (Ideal.Quotient.mk P.ideal f)

def genPt (P : ArithVariety n) : Coord n → FunField P := fun v ↦ val P (X v)

def IsLive (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) : Prop :=
  ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal

def chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) : Subalgebra ℤ (FunField P) :=
  chartRingZ (genPt P) c

def chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) : FunField P :=
  ∏ k, genPt P ⟨k, c k⟩ ^ a k

def IsHomogOfDeg (P : ArithVariety n) (a : ι → ℤ) (x : FunField P) : Prop :=
  ∃ (f g : MvPolynomial (Coord n) ℤ) (df dg : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f df ∧
    IsWeightedHomogeneous (coordDeg n) g dg ∧ g ∉ P.ideal ∧ (∀ k, (df k : ℤ) - dg k = a k) ∧
    x = val P f / val P g

def conePoints {κ : Type} [Fintype κ] [DecidableEq κ] {m : κ → ℕ}
    (I : Ideal (MvPolynomial (Coord m) ℤ)) (F : Type*) [CommRing F] : Set (Cone m F) :=
  {z | BlockNonzero z ∧ ∀ f ∈ I, evalCone z f = 0}

theorem points_eq_conePoints (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := rfl

structure GenSystem (P : ArithVariety n) where

  r : ℕ

  f : Fin r → MvPolynomial (Coord n) ℤ

  δ : Fin r → ι → ℕ
  homog : ∀ i, IsWeightedHomogeneous (coordDeg n) (f i) (δ i)
  span_eq : Ideal.span (Set.range f) = P.ideal

structure AddBlockData (P : ArithVariety n) where

  deg : ι → ℤ

  m : ℕ

  x : Fin (m + 1) → FunField P
  homog : ∀ j, IsHomogOfDeg P deg (x j)
  chart : ∀ c, IsLive P c → ∀ j, x j * chartPow P c (-deg) ∈ chartRing P c
  unit : ∀ c, IsLive P c → ∃ u : Fin (m + 1) → FunField P, (∀ j, u j ∈ chartRing P c) ∧
    ∑ j, u j * (x j * chartPow P c (-deg)) = 1

namespace AddBlockData

end AddBlockData

open AddBlockData

structure ChartForms {P : ArithVariety n} (D : AddBlockData P) where

  d : ι → ℕ
  d_pos : ∀ k, 1 ≤ d k
  dn_nonneg : ∀ k, 0 ≤ (d k : ℤ) + D.deg k

  g : ((k : ι) → Fin (n k + 1)) → Fin (D.m + 1) → MvPolynomial (Coord n) ℤ
  g_homog : ∀ c, IsLive P c → ∀ j,
    IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ ((d k : ℤ) + D.deg k).toNat)
  g_val : ∀ c, IsLive P c → ∀ j, val P (g c j) = val P (chartMonomial c d) * D.x j
  g_dead : ∀ c, ¬ IsLive P c → ∀ j, g c j = 0

section Metric

variable {P : ArithVariety n} {D : AddBlockData P}

def den (G : ChartForms D) (Γ : GenSystem P) (z : Cone n ℂ) : ℝ :=
  (∑ c, ∑ j, ‖evalCone z (G.g c j)‖ ^ 2) +
    ∑ i, ‖evalCone z (Γ.f i)‖ ^ 2 *
      ∏ k, l2Norm (z k) ^ (2 * ((G.d k : ℤ) + D.deg k - Γ.δ i k))

end Metric

variable (n) in

def pullFS (k₀ : ι) : HermLine n :=
  HermLine.pullback (fun _ : Unit ↦ k₀) (fun _ _ _ ↦ Subsingleton.elim _ _)
    (HermLine.standard (n ∘ fun _ : Unit ↦ k₀))

section OneBlock

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

def hermNorm {i : ℕ} (H : Matrix (Fin i) (Fin i) ℂ) (w : Fin i → ℂ) : ℝ :=
  Real.sqrt (star w ⬝ᵥ (H *ᵥ w)).re

end OneBlock

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
