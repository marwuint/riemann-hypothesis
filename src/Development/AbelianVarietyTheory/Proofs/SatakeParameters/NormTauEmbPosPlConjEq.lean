module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

section General

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem SamePrime.lt_one_imp {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) (hx : ‖ρ x‖ < 1) : ‖ρ' x‖ < 1 := by
  have hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1 := fun σ a ha =>
    le_antisymm (norm_int_le σ a) (not_lt.1 ha)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    ⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by
      have := natCast_mem_primeOf ρ
      rw [hb, Ideal.mem_bot] at this
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩
  obtain ⟨n, d, e | e⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1 := fun c => hd ((h _).2 c)
    have e' : x * ((d : 𝓞 E) : E) = (n : E) := e
    have hn : ‖ρ (n : E)‖ < 1 := by
      rwa [← e', map_mul, norm_mul, hone ρ _ hd, mul_one]
    have hn' := (h n).1 hn
    rwa [← e', map_mul, norm_mul, hone ρ' _ hd', mul_one] at hn'
  · exfalso
    have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have e' : x * (n : E) = ((d : 𝓞 E) : E) := e
    apply hd
    rw [← e', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx

theorem SamePrime.norm_eq {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) : ‖ρ x‖ = ‖ρ' x‖ := by
  let u : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective
  let w : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective
  have hu (x) : u x = ‖ρ x‖ := rfl
  have hw (x) : w x = ‖ρ' x‖ := rfl
  have he : u.IsEquiv w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a =>
    ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have h1 : c = 1 := by
    have h2 := congrFun hce (l : E)
    simp only [hu, hw, hn] at h2
    have h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ) := by rw [h2, Real.rpow_one]
    exact (Real.rpow_right_inj (by positivity) (by
      exact (inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3
  simpa only [hu, hw, h1, Real.rpow_one] using congrFun hce x

end General

theorem norm_tauEmb_posPl_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ‖tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y)‖ = ‖tauEmb D lam (tauPl D z) y‖ := by
  intro D p _ lam h z y
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])
  have h1 := SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)
  have h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y := by
    change rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _
    rw [hcc]
  rw [h2] at h1
  rwa [← coe_rhoH, ← coe_rhoH]

end GlobalTheory.KerStd
