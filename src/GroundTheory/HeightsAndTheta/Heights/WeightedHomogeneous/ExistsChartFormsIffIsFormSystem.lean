import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

namespace AddBlockData

def ofObjects (D : Heights.AddBlockData P) : AddBlockData P where
  deg := D.deg
  m := D.size
  x j := funFieldEquiv P (D.elt j)
  homog j := (isOfDegree_iff P D.deg (D.elt j)).1 (D.elt_deg j)
  chart c hc j := by
    rw [← funFieldEquiv_div_chartPow, funFieldEquiv_mem_chartRing_iff]
    exact D.chart_mem c hc j
  unit c hc := by
    obtain ⟨u, hu, hsum⟩ := D.generating c hc
    refine ⟨fun j ↦ funFieldEquiv P (u j), fun j ↦ (funFieldEquiv_mem_chartRing_iff P c _).2 (hu j),
      ?_⟩
    simp only [← funFieldEquiv_div_chartPow, ← map_mul, ← map_sum, hsum, map_one]

def toObjects (D : AddBlockData P) : Heights.AddBlockData P where
  deg := D.deg
  size := D.m
  elt j := (funFieldEquiv P).symm (D.x j)
  elt_deg j := (isOfDegree_iff P D.deg _).2 (by rw [RingEquiv.apply_symm_apply]; exact D.homog j)
  chart_mem c hc j := by
    rw [← funFieldEquiv_mem_chartRing_iff, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply]
    exact D.chart c hc j
  generating c hc := by
    obtain ⟨u, hu, hsum⟩ := D.unit c hc
    refine ⟨fun j ↦ (funFieldEquiv P).symm (u j), fun j ↦ ?_, ?_⟩
    · rw [← funFieldEquiv_mem_chartRing_iff, RingEquiv.apply_symm_apply]
      exact hu j
    · apply (funFieldEquiv P).injective
      simp only [map_sum, map_mul, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply, map_one]
      exact hsum

end AddBlockData

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

omit [Fintype ι] in

theorem isWeightedHomogeneous_toNat {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} {a : ι → ℤ}
    (h : ∃ δ : ι → ℕ, IsWeightedHomogeneous (coordDeg n) f δ ∧ ∀ k, (δ k : ℤ) = d k + a k) :
    IsWeightedHomogeneous (coordDeg n) f (fun k ↦ ((d k : ℤ) + a k).toNat) := by
  obtain ⟨δ, hδ, hδk⟩ := h
  have e : (fun k ↦ ((d k : ℤ) + a k).toNat) = δ := by
    funext k
    have := hδk k
    omega
  rw [e]
  exact hδ

namespace ChartForms

variable {D : AddBlockData P}

def ofFormSystem {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) : ChartForms (ofObjects D) where
  d := d
  d_pos := h.pos
  dn_nonneg := h.nonneg
  g := g
  g_homog c _ j := isWeightedHomogeneous_toNat (h.homog c j)
  g_val c hc j := by
    show val P (g c j) = val P (chartMonomial c d) * funFieldEquiv P (D.elt j)
    rw [← funFieldEquiv_mkF, ← funFieldEquiv_mkF, ← map_mul, h.value c hc j]
  g_dead c hc j := h.dead c hc j

end ChartForms

section Metric

variable {D : AddBlockData P}

theorem den_eq (G : ChartForms D) (Γ : GenSystem P) :
    den G Γ = (toObjects D).den G.d G.g Γ.f Γ.δ := rfl

theorem den_ofFormSystem {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) {r : ℕ} {f : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hf : P.IsHomogGenerators f δ) :
    D.den d g f δ = den (ChartForms.ofFormSystem h) (GenSystem.ofIsHomogGenerators hf) := rfl

end Metric

omit [DecidableEq ι] in

theorem hermLine_pow_metric (A : HermLine n) (m : ℕ) (z : Cone n ℂ) :
    (A.pow m).metric z = A.metric z ^ m := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
