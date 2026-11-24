module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.OrbRing
public import Formalism.SatakeDualWeyl.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix
open Formalism.UG

namespace GlobalTheory.WittTransitivity

variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)

theorem hform_sub_left (x y z : Fin M → A) :
    hform c J (x - y) z = hform c J x z - hform c J y z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y z : Fin M → A) :
    hform c J x (y - z) = hform c J x y - hform c J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_left (a : A) (x z : Fin M → A) :
    hform c J (a • x) z = c a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_right (a : A) (x z : Fin M → A) :
    hform c J x (a • z) = a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem conj_hform (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by

  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hform_eq_sum (x y : Fin M → A) :
    hform c J x y = ∑ j, hform c J x (Pi.single j 1) * y j := by
  have key : ∀ j, hform c J x (Pi.single j 1) = ∑ i, c (x i) * J i j := by
    intro j
    simp [Formalism.UG.hform, Pi.single_apply]
  simp_rw [key]
  simpa only [Formalism.UG.hform, Finset.sum_mul] using Finset.sum_comm

theorem exists_mem_UJ (hdet : IsUnit J.det) (g : Matrix (Fin M) (Fin M) A)
    (hg : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z) :
    ∃ G ∈ UJ c J, (G : Matrix (Fin M) (Fin M) A) = g := by
  apply PI.VolStabSW.OrbR.mem_UJ_of <;> assumption

theorem exists_reflection (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hdet : IsUnit J.det) (x x' : Fin M → A) (hx : hform c J x x = hform c J x' x')
    (hs : IsUnit (hform c J x x - hform c J x' x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  set s := hform c J x x - hform c J x' x with hs_def
  obtain ⟨su, hsu⟩ := hs
  set b : A := ↑su⁻¹ with hb_def
  have hbs : b * s = 1 := by rw [hb_def, ← hsu, Units.inv_mul]
  have hcb : c b * c s = 1 := by rw [← map_mul, hbs, map_one]
  set v := x - x' with hv
  have hvv : hform c J v v = s + c s := by
    have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
    have e1 : c s = hform c J x x - hform c J x x' := by
      rw [hs_def, map_sub, hxx, conj_hform c J hc hJ]
    rw [hv, hform_sub_left, hform_sub_right, hform_sub_right, e1, hs_def, ← hx]
    ring
  set g : Matrix (Fin M) (Fin M) A :=
    1 - Matrix.of (fun k j => b * v k * hform c J v (Pi.single j 1)) with hg_def
  have hgy : ∀ y, g *ᵥ y = y - (b * hform c J v y) • v := by
    intro y
    rw [hform_eq_sum c J v y]
    ext k
    rw [hg_def, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpres : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z := by
    intro y z
    rw [hgy, hgy, hform_sub_left, hform_sub_right, hform_sub_right, hform_smul_left,
      hform_smul_left, hform_smul_right, hform_smul_right, map_mul,
      conj_hform c J hc hJ v y, hvv]
    linear_combination (hform c J y v * hform c J v z * c b) * hbs +
      (hform c J y v * hform c J v z * b) * hcb
  obtain ⟨G, hG, hGg⟩ := exists_mem_UJ c J hdet g hpres
  refine ⟨G, hG, ?_⟩
  have hvx : hform c J v x = s := by rw [hv, hform_sub_left, hs_def]
  rw [hGg, hgy, hvx, hbs, one_smul, hv, sub_sub_cancel]

theorem exists_norm_one (hc : ∀ a, c (c a) = a) (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a)
    (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0) (hθ : ∃ θ, IsUnit (θ - c θ))
    (b t : A) (hcb : c b = b) (hb : IsUnit b) :
    ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
  have hN : ∀ a : A, a * c a ≠ 0 → IsUnit (a * c a) := fun a ha =>
    hf _ (by rw [map_mul, hc, mul_comm]) ha
  by_cases h1 : (b - t) * c (b - t) = 0
  · by_cases h1' : (b + t) * c (b + t) = 0
    · rw [map_sub, hcb] at h1
      rw [map_add (f := _), hcb] at h1'
      have htc : t + c t = 0 := (h2.mul hb).mul_left_cancel (by linear_combination h1' - h1)
      have hb2 : b * b = t * t :=
        sub_eq_zero.mp (h2.mul_left_cancel (by linear_combination h1 + h1' - 2 * t * htc))
      have ht : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← hb2]; exact hb.mul hb)
      have key : ∀ w : A, IsUnit (w * c w) → IsUnit (w - c w) → IsUnit (w + c w) →
          ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
        intro w hw hm hp
        obtain ⟨e, he⟩ := isUnit_of_mul_isUnit_right hw
        have h0 : c (↑e⁻¹ : A) * w = 1 := by
          have h6 := congrArg c (Units.inv_mul e)
          rwa [map_mul, he, hc, map_one] at h6
        refine ⟨w * ↑e⁻¹, ?_, ?_⟩
        · rw [map_mul]
          linear_combination ((↑e⁻¹ : A) * c w) * h0 - (↑e⁻¹ : A) * he + Units.inv_mul e
        · have hprod : IsUnit ((w * b - c w * t) * (c w * b + w * t)) := by
            convert ((hb.mul ht).mul hm).mul hp using 1
            linear_combination (w * c w) * hb2
          have e2 : b - c (w * ↑e⁻¹) * t = c ↑e⁻¹ * (w * b - c w * t) := by
            rw [map_mul]
            linear_combination (-b) * h0
          rw [e2]
          exact (isUnit_of_mul_isUnit_left (by rw [h0]; exact isUnit_one)).mul
            (isUnit_of_mul_isUnit_left hprod)
      obtain ⟨θ, hθu⟩ := hθ
      have hcδ : c (θ - c θ) = -(θ - c θ) := by rw [map_sub, hc]; ring
      by_cases hd : (1 + (θ - c θ)) * c (1 + (θ - c θ)) = 0
      · rw [map_add (f := _), map_one, hcδ] at hd
        apply key (2 + (θ - c θ))
        · convert hf 3 (map_ofNat c 3) h3 using 1
          rw [map_add (f := _), map_ofNat, hcδ]
          linear_combination hd
        · convert h2.mul hθu using 1
          rw [map_add (f := _), map_ofNat, hcδ]
          ring
        · convert h2.mul h2 using 1
          rw [map_add (f := _), map_ofNat, hcδ]
          ring
      · apply key (1 + (θ - c θ)) (hN _ hd)
        · convert h2.mul hθu using 1
          rw [map_add (f := _), map_one, hcδ]
          ring
        · convert h2 using 1
          rw [map_add (f := _), map_one, hcδ]
          ring
    · refine ⟨-1, by rw [map_neg, map_one]; ring, ?_⟩
      convert isUnit_of_mul_isUnit_left (hN _ h1') using 1
      rw [map_neg, map_one]
      ring
  · refine ⟨1, by rw [map_one, one_mul], ?_⟩
    convert isUnit_of_mul_isUnit_left (hN _ h1) using 1
    rw [map_one, one_mul]

theorem witt_transitive (A : Type) [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a)
    (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a) (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0)
    (hθ : ∃ θ, IsUnit (θ - c θ)) (M : ℕ) (J : Matrix (Fin M) (Fin M) A)
    (hJ : ∀ i j, c (J j i) = J i j) (hdet : IsUnit J.det) (x x' : Fin M → A)
    (hx : hform c J x x = hform c J x' x') (hb : IsUnit (hform c J x x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
  obtain ⟨u, hu, hut⟩ :=
    exists_norm_one c hc hf h2 h3 hθ (hform c J x x) (hform c J x' x) hxx hb
  have hux : hform c J x x = hform c J (u • x') (u • x') := by
    rw [hform_smul_left, hform_smul_right, ← hx]
    linear_combination (-(hform c J x x)) * hu
  obtain ⟨g1, hg1, hg1x⟩ := exists_reflection c J hc hJ hdet x (u • x') hux
    (by rw [hform_smul_left]; exact hut)
  obtain ⟨g2, hg2, hg2e⟩ := exists_mem_UJ c J hdet (c u • (1 : Matrix (Fin M) (Fin M) A))
    (by
      intro y z
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hform_smul_left, hform_smul_right, hc]
      linear_combination (hform c J y z) * hu)
  refine ⟨g2 * g1, mul_mem hg2 hg1, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg1x, hg2e]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  rw [mul_comm, hu, one_smul]

end GlobalTheory.WittTransitivity
