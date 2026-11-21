import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EvenCeil
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

noncomputable section

namespace GlobalTheory.Mem.Num

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits NumberField

structure admitted (C : FC) : Prop where
  fixed : C.Fixed
  eP : C.T.eP = 12
  Cp : C.T.Cp = 1
  cTO : C.T.cTO = 377
  Cc : C.Cc = 2
  CLw : C.P.CLw = 4455
  Cj0 : C.P.Cj0 = 405
  cw : C.P.cw = 9 / 10
  CYL : C.P.CYL = 9
  CccK : C.P.CccK = 1
  CetaF : C.P.CetaF = 6
  pos : ∀ c ∈ C.P.list, 0 < c
  CP : 1 ≤ C.T.CP
  Cb : 0 ≤ C.T.Cb
  ChT : 1 ≤ C.T.ChT
  CbN : 1 ≤ C.T.CbN
  CGam : 0 < C.CGam
  GK : C.GK.Nonneg
  La : 1 ≤ C.GK.La

def RChosen (C : FC) (s : Scale) (R : Ranks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
    R.k = kAt s ∧ R.m = mAt s ∧ R.t = tAt C s R.n ∧ (R.o : ℝ) ≤ C.P.Cpde

def dlogH {R : Ranks} (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))) 1 /
    DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) 1).re

structure HChosen (C : FC) (s : Scale) {R : Ranks} (H : Host R) : Prop where
  ranks : RChosen C s R
  q_lo : Real.exp (s.x ^ (s.ez / 5) / 2) < (H.q : ℝ)
  q_hi : (H.q : ℝ) ≤ Real.exp (s.x ^ (s.eps / 5))
  d_lo : Real.exp (s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2) < (H.d : ℝ)
  d_hi : (H.d : ℝ) ≤ Real.exp (s.x ^ (s.eps / 5) * Real.log s.x ^ 2)
  dlog : |dlogH H| ≤ s.x ^ s.eps
  split : ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound
  tt : s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) ∧ (H.TT.card : ℝ) ≤ 2 * s.delta1 * R.n
  t2 : s.x ^ (-s.eps) ≤ (H.T2.card : ℝ) / R.n
  Lw : H.Lw = LwAt C s
  CT2 : H.CT2 = C.CT2
  ccK : H.ccK = ⊤
  pde_log : Real.log H.pde ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d) ∧
    Real.log H.pde' ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d)
  pde_split : (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E
  g_win : ∀ i, YAt s ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * YAt s
  g_norm : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_mod : ∀ i, H.g i % (H.QS * H.q * H.d) = 1
  level_split : ∀ p ∈ H.levelPrimes, H.cls p = .splitK
  J_le : s.J ≤ C.P.Cpde
  QS_le : (H.QS : ℝ) ≤ C.P.Cpde * R.n

structure InRange (C : FC) (s : Scale) {R : Ranks} (H : Host R) (q0 : ℕ) : Prop extends HChosen C s H where
  thickCard_bound : 4 * H.Lw * H.T2.card ≤ R.n0
  automorphicMembership_prime_fact : q0.Prime
  automorphicMembership_level_fact : q0 ∈ H.levelPrimes
  q0_mod_eq_one_of_dvd_condE : q0 % (H.QS * H.q * H.d) = 1
  automorphicMembership_ge_fact : 5 ≤ q0
  automorphicMembership_log_fact : Real.log q0 ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d)
  q0_ne_two_and_ne_q_and_ne_d : q0 ≠ H.pde ∧ q0 ≠ H.pde'

namespace Chosen

theorem iota_inv (φ : Formalism.HC.Frame) (t : φ.A) : φ.iotaInv (φ.tau1 t).2 = t := rfl

end Chosen

end GlobalTheory.Mem.Num

end
