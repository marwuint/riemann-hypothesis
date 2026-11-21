import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

abbrev hessL (L : HermLB p) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess (L.φ σ) (pick (L.φ σ).isLB y) y

variable {c : AlgChart p σ D} {y : CxPts p σ}

theorem c1F_eq_matForm_hessL (hX : IsRegVar p D) (L : HermLB p) (hy : y ∈ c.e.source) :
    c1F hX σ L ⟨(c, y), hy⟩ = matForm D (hessL L c y) := by
  have hd := (L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)
  change ofValues _ = kappa • ∑ a, rowForm a _
  simp only [ofValues, rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem hessL_tens (L M : HermLB p) (hy : y ∈ c.e.source) : hessL (L.tens M) c y = hessL L c y + hessL M c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  exact (c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)).trans (FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb)

end GlobalTheory.ChernTop
