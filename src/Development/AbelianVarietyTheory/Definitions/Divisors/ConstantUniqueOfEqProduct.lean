import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finite_levQc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (l : Level H) : Finite (LevQc Dw l) := by
  have hM : Mfr l ≠ ⊥ := by
    intro h
    have h₁ : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := (Mfr l).finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul (Mfr l) (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem hatC_phiHat {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}
    (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    inC c (phiHat c φ q) = hatC l (fun x => inC c (φ x)) q := by
  haveI := finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  have hz : inC c (zetaM c) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    rw [zetaM, map_pow]
    show zeta l.M' ^ (l.M' / l.M) = _
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have h0 : 0 < l.M := by have := l.three_le; omega
    have h1 : l.M' ≠ 0 := Nat.lcm_ne_zero h0.ne' l.A_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by rintro h; apply h1; rw [hm, Nat.cast_eq_zero.1 h, mul_zero]
    have h3 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [zeta, ← Complex.exp_nat_mul, hm, Nat.mul_div_cancel_left _ h0]
    congr 1
    push_cast
    field_simp
  rw [phiHat, hatC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀, hz]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

end

end GlobalTheory.AdTh.PairModel
