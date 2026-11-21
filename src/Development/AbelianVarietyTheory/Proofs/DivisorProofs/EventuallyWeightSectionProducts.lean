import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnramPtsDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspMulUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ' {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem eq_of_mem_secZ {e e' : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    (hf' : f ∈ GlobalTheory.AllWt.secZ Xo c e') (h0 : f ≠ 0) : e = e' := by
  classical
  by_contra hne
  apply h0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  funext p y
  let u0 : (c.F)ˣ := Units.mk0 2 two_ne_zero
  let t : Ix Dw → (p.R)ˣ := Pi.mulSingle i (Units.map (algebraMap c.F p.R : c.F →* p.R) u0)
  have hw : ∀ d : Ix Dw → ℤ, ((∏ j, t j ^ d j : (p.R)ˣ) : p.R) = algebraMap c.F p.R ((2 : c.F) ^ d i) := by
    intro d
    rw [Finset.prod_eq_single i]
    · simp only [t, Pi.mulSingle_eq_same, ← map_zpow, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
        u0, Units.val_mk0]
    · intro j _ hj
      simp [t, Pi.mulSingle_eq_of_ne hj]
    · simp
  obtain ⟨y', hy'⟩ := GlobalTheory.SecSeparation.exists_frBor y t
  have e1 := hf.2 p t y y' hy'
  have e2 := hf'.2 p t y y' hy'
  rw [hw] at e1 e2
  have hne2 : (2 : c.F) ^ e i - (2 : c.F) ^ e' i ≠ 0 := by
    intro h
    apply hi
    have h1 : algebraMap ℚ c.F ((2 : ℚ) ^ e i) = algebraMap ℚ c.F ((2 : ℚ) ^ e' i) := by
      rw [map_zpow₀, map_zpow₀, map_ofNat]
      exact sub_eq_zero.1 h
    exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℚ c.F).injective h1)
  have hu : IsUnit (algebraMap c.F p.R ((2 : c.F) ^ e i - (2 : c.F) ^ e' i)) := (IsUnit.mk0 _ hne2).map _
  show f p y = 0
  refine hu.mul_right_eq_zero.1 ?_
  rw [map_sub, sub_mul, ← e1, ← e2, sub_self]

end GlobalTheory.CuspMulUnit

namespace GlobalTheory.CuspMulUnit

theorem fj_mul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (hE : 1 < Module.finrank ℚ E / 2) {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) (hQ : X.IsSec la' Q) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x) (hx : x ∈ X.dom) :
    X.fj (la + la') ξ 0 (P * Q) x = 0 := by
  have hPs := hP.1.1
  have hm := ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds (E := E) r X la la' P Q hPs hQ (GlobalTheory.CuspFrom.isModerate _ hE hPs)
    (GlobalTheory.CuspFrom.isModerate _ hE hQ) ξ hξ x hx 0
  have hz : ∀ ν, X.fj la ξ ν P x * X.fj la' ξ (0 - ν) Q x = 0 := by
    intro ν
    by_cases h1 : X.fj la ξ ν P x = 0
    · rw [h1, zero_mul]
    by_cases h2 : X.fj la' ξ (0 - ν) Q x = 0
    · rw [h2, mul_zero]
    exfalso
    have a1 := GlobalTheory.CuspFrom.freqNonneg _ hE hPs ξ hξ ν x hx h1
    have a2 := GlobalTheory.CuspFrom.freqNonneg _ hE hQ ξ hξ (0 - ν) x hx h2
    have hν : ν = 0 := funext fun τ => le_antisymm (by have := a2 τ; simp at this; exact this) (a1 τ)
    subst hν
    exact h1 (hP.2 ξ hξ x hx)
  simp only [hz] at hm
  exact hm.unique hasSum_zero

end GlobalTheory.CuspMulUnit
