import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem big_of_le_nV (D : Formalism.BasicNotions.D7) (k : Fin 2) {n : ℕ} (hn : n ≤ D.R.nV) : 16 * n ^ 2 < D.host.g k := by
  have hg : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  have hq := D.host.qd_big
  have ht : 0 < D.R.t := D.R.t_odd.pos
  have hr : 1 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; have := D.R.two_le_m; omega
  have h2 : 2 ≤ D.host.g k := (D.host.g_prime k).two_le
  have hQ0 : 0 < D.host.QS := by
    rcases Nat.eq_zero_or_pos D.host.QS with h | h
    · rw [h] at hg; simp at hg; omega
    · exact h
  have h16 : 16 ≤ D.host.QS :=
    Nat.le_of_dvd hQ0 ((pow_dvd_pow 2 (m := 4) (by have := D.host.two_le_e; omega)).trans D.host.tower_dvd)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have := Nat.mod_add_div (D.host.g k) (D.host.QS * D.host.q * D.host.d)
    rw [hg] at this
    exact ⟨D.host.g k / (D.host.QS * D.host.q * D.host.d), Nat.sub_eq_of_eq_add' this.symm⟩
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hn' : n ≤ 4 * D.R.t * D.R.r + 1 := by
    unfold Formalism.BasicNotions.Ranks.nV at hn
    nlinarith
  have hq1 : n ≤ D.host.q := by omega
  have hd1 : n ≤ D.host.d := by omega
  have h5 : n * n ≤ D.host.q * D.host.d := Nat.mul_le_mul hq1 hd1
  have h6 : 16 * (D.host.q * D.host.d) ≤ D.host.QS * D.host.q * D.host.d := by
    rw [mul_assoc D.host.QS]
    exact Nat.mul_le_mul_right _ h16
  rw [sq]
  omega

end DiscreteGroups.sglob.DzType
