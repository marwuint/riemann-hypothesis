module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GaussPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a => ε a = false) = Finset.univ.filter fun a => ¬ ε a = true := by
    ext a; simp
  rwa [h2]

theorem bS_herm (X : Fin n → ℝ) (h : ℝ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : (bS X h b).IsHermitian := by
  have hD : (diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)))ᴴ = diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal _
  unfold bS Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, hb.eq, Matrix.mul_assoc]

theorem derivative_vacuum_of_parts (hG : GaussPart) (hH : GroupPart) : DerivativeVacuumDilations := by
  intro m n ε c t p q e sL ρ hL X a hA y r
  obtain ⟨hadd, ha0, hup, hcont, hupmul, hdec, hconj, hcellinv, hdense, hF0⟩ := hH n X a hA
  obtain ⟨C, hC0, hcell⟩ := hL.cell
  have hpq : p + q = m := by
    rcases hL.sign with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact cnt_add ε
    · rw [add_comm]; exact cnt_add ε
  have hneg : ∀ h : ℝ, a (-h) * a h = 1 := by
    intro h; rw [← hadd, neg_add_cancel, ha0]

  have L1 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 →
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) y) 0 := by
    intro Q y hy
    obtain ⟨y₁, g, b, hy₁, hb, hg, rfl⟩ := hdec y hy
    have hfun : (fun h => sL Q (y₁ * g * a h)) = fun h => (F0 p q e y₁ * C) *
        (Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) := by
      funext h
      have e1 : y₁ * g * a h = (y₁ * a (-h)) * (a h * g * a h) := by
        calc y₁ * g * a h = y₁ * (a (-h) * a h) * g * a h := by rw [hneg, mul_one]
          _ = _ := by group
      have e2 : F0 p q e (y₁ * a (-h)) = F0 p q e y₁ * F0 p q e (a (-h)) := by
        rw [← hL.vac, hL.law 1 _ _ hy₁, hL.vac]
      have e3 : F0 p q e (a (-h)) = Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) := by
        rw [hF0, hpq]
      rw [e1, hL.law Q _ _ (hupmul y₁ hy₁ (-h)), e2, e3, hcell Q _ _ (bS_herm X h hb) (hconj g b hg h)]
      ring
    rw [hfun]
    have hv : sL (dil c X Q) (y₁ * g) = (F0 p q e y₁ * C) * secN ε c t (dil c X Q) b := by
      rw [hL.law _ _ _ hy₁, hcell _ _ _ hb hg]; ring
    rw [hv]
    exact (hG m n ε c t hL.cpos X b hb Q).const_mul _

  have L2 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∀ s,
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y hy s
    have h0 := L1 Q (y * a s) (hcellinv y hy s)
    have h0' : HasDerivAt (fun h => sL Q (y * a s * a h)) (sL (dil c X Q) (y * a s)) (s - s) := by
      rw [sub_self]; exact h0
    have h1 := HasDerivAt.comp_sub_const s s h0'
    have hf : (fun x => sL Q (y * a x)) = fun x => sL Q (y * a s * a (x - s)) := by
      funext x
      rw [mul_assoc, ← hadd, add_sub_cancel]
    rwa [hf]
  have hjc : ∀ (Q : PX m n), Continuous (fun z : GR n × ℝ => sL Q (z.1 * a z.2)) := fun Q =>
    (hL.cont Q).comp (continuous_fst.mul (hcont.comp continuous_snd))

  have L3 : ∀ (Q : PX m n) (s : ℝ) (y : GR n),
      sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) := by
    intro Q s
    have hc1 : Continuous fun y : GR n => sL Q (y * a s) - sL Q y :=
      ((hL.cont Q).comp (continuous_id.mul continuous_const)).sub (hL.cont Q)
    have hc2 : Continuous fun y : GR n => ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hjc (dil c X Q)) continuous_const
    intro y0
    refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) y0
    intro y hy
    show sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u)
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a x)) x :=
      fun x _ => L2 Q y hy x
    have hint : IntervalIntegrable (fun u => sL (dil c X Q) (y * a u)) volume 0 s :=
      ((hL.cont (dil c X Q)).comp (continuous_const.mul hcont)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, ha0, mul_one]
  have L4 : ∀ (Q : PX m n) (y : GR n) (s : ℝ),
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y s
    have hgc : Continuous fun u => sL (dil c X Q) (y * a u) := (hL.cont _).comp (continuous_const.mul hcont)
    have h1 := (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h2 := h1.const_add (sL Q y)
    have hf : (fun h => sL Q (y * a h)) = fun x => sL Q y + ∫ u in (0 : ℝ)..x, sL (dil c X Q) (y * a u) := by
      funext x
      rw [← L3 Q x y]; ring
    rwa [hf]
  have L5 : ∀ k : ℕ, iteratedDeriv k (fun s => F0 p q e (y * a s)) = fun s => sL ((dil c X ^ k) 1) (y * a s) := by
    intro k
    induction k with
    | zero => funext s; simp [hL.vac]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(L4 _ y s).deriv, pow_succ', Module.End.mul_apply]
  refine ⟨?_, ?_⟩
  · rw [L5 r]
    have := L4 ((dil c X ^ r) 1) y 0
    rwa [ha0, mul_one, ← Module.End.mul_apply, ← pow_succ'] at this
  · rw [L5 r]
    show sL ((dil c X ^ r) 1) (y * a 0) = _
    rw [ha0, mul_one]

end PositivityTheory.Rg.Sw.AbsSt.DF
