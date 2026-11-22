import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace ArithVariety

variable (P : ArithVariety n)

def IsLive (c : (k : ι) → Fin (n k + 1)) : Prop :=
  ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal

def chartRing (c : (k : ι) → Fin (n k + 1)) : Subring P.FunField :=
  Subring.closure (Set.range (P.chartCoord c))

def chartPow (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) : P.FunField :=
  ∏ k, P.mkF (X ⟨k, c k⟩) ^ a k

def IsOfDegree (a : ι → ℤ) (x : P.FunField) : Prop :=
  ∃ (f g : MvPolynomial (Coord n) ℤ) (δf δg : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
    IsWeightedHomogeneous (coordDeg n) g δg ∧ (∀ k, (δf k : ℤ) - δg k = a k) ∧ g ∉ P.ideal ∧
    x = P.mkF f / P.mkF g

structure IsHomogGenerators {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) :
    Prop where
  homog : ∀ i, IsWeightedHomogeneous (coordDeg n) (G i) (δ i)
  span_eq : Ideal.span (Set.range G) = P.ideal

end ArithVariety

structure AddBlockData (P : ArithVariety n) where

  deg : ι → ℤ

  size : ℕ

  elt : Fin (size + 1) → P.FunField
  elt_deg : ∀ j, P.IsOfDegree deg (elt j)
  chart_mem : ∀ c, P.IsLive c → ∀ j, elt j / P.chartPow c deg ∈ P.chartRing c
  generating : ∀ c, P.IsLive c → ∃ u : Fin (size + 1) → P.FunField,
    (∀ j, u j ∈ P.chartRing c) ∧ ∑ j, u j * (elt j / P.chartPow c deg) = 1

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

def extSizes : Option ι → ℕ := fun o ↦ o.elim D.size n

def extVal : Coord D.extSizes → P.FunField
  | ⟨none, j⟩ => D.elt j
  | ⟨some k, i⟩ => P.mkF (X ⟨k, i⟩)

def extMap : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Option ι) P.FunField :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (D.extVal v) * X v.1

def extIdeal : Ideal (MvPolynomial (Coord D.extSizes) ℤ) := RingHom.ker D.extMap

structure IsFormSystem (d : ι → ℕ)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) : Prop where
  pos : ∀ k, 1 ≤ d k
  nonneg : ∀ k, 0 ≤ (d k : ℤ) + D.deg k
  homog : ∀ c j, ∃ δ : ι → ℕ,
    IsWeightedHomogeneous (coordDeg n) (g c j) δ ∧ ∀ k, (δ k : ℤ) = d k + D.deg k
  value : ∀ c, P.IsLive c → ∀ j, P.mkF (g c j) = P.mkF (chartMonomial c d) * D.elt j
  dead : ∀ c, ¬ P.IsLive c → ∀ j, g c j = 0

def den (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) (z : Cone n ℂ) : ℝ :=
  (∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2) +
    ∑ i, ‖evalCone z (G i)‖ ^ 2 * ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k))

end AddBlockData

namespace HermLine

def pow (A : HermLine n) (m : ℕ) : HermLine n where
  deg := m • A.deg
  metric z := A.metric z ^ m
  metric_pos z hz := pow_pos (A.metric_pos z hz) m
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
  metric_smooth := A.metric_smooth.pow m

def mul (A B : HermLine n) : HermLine n where
  deg := A.deg + B.deg
  metric z := A.metric z * B.metric z
  metric_pos z hz := mul_pos (A.metric_pos z hz) (B.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, B.metric_smul c z hc hz]
    have h : ∏ k, ‖c k‖ ^ (A.deg + B.deg) k = (∏ k, ‖c k‖ ^ A.deg k) * ∏ k, ‖c k‖ ^ B.deg k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [Pi.add_apply, zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
    rw [h]
    ring
  metric_smooth := A.metric_smooth.mul B.metric_smooth

def inv (A : HermLine n) : HermLine n where
  deg := -A.deg
  metric z := (A.metric z)⁻¹
  metric_pos z hz := inv_pos.mpr (A.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]
  metric_smooth := A.metric_smooth.inv fun z hz ↦ (A.metric_pos z hz).ne'

end HermLine

namespace IntegralSection

variable {P : ArithVariety n} {a b : ι → ℤ}

def toFun (s : IntegralSection P a) : P.FunField := P.mkF s.num / P.mkF s.den

def cast (h : a = b) (s : IntegralSection P a) : IntegralSection P b where
  num := s.num
  den := s.den
  numDeg := s.numDeg
  denDeg := s.denDeg
  num_isHomogeneous := s.num_isHomogeneous
  den_isHomogeneous := s.den_isHomogeneous
  deg_eq k := by subst h; exact s.deg_eq k
  den_not_mem := s.den_not_mem
  regular c hc := by subst h; exact s.regular c hc

end IntegralSection

def blockIncl (k₀ : ι) : Coord (fun _ : Unit ↦ n k₀) → Coord n := fun v ↦ ⟨k₀, v.2⟩

variable {K : Type*} [Field K] [NumberField K] {e r : ℕ}

end

end GroundTheory.Heights₂.Heights
