import Mathlib

open PowerSeries

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods

section Expansion

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

def step (v : A⟦X⟧) : A⟦X⟧ :=
  1 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X ^ 3 * v ^ 2 + C W.a₄ * X ^ 4 * v ^ 2
    + C W.a₆ * X ^ 6 * v ^ 3

def vSer : A⟦X⟧ := mk fun n => coeff n ((step W)^[n + 1] 0)

def wSer : A⟦X⟧ := X ^ 3 * vSer W

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma nodal_map_sub_eq_X_mul_sub_mul (u v : A⟦X⟧) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v =
      X * (u - v) * (C W.a₁ + C W.a₂ * X + C W.a₃ * X ^ 2 * (u + v) + C W.a₄ * X ^ 3 * (u + v)
        + C W.a₆ * X ^ 5 * (u ^ 2 + u * v + v ^ 2)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step
  ring

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_succ_dvd_sub_of_X_pow_dvd {k : ℕ} {u v : A⟦X⟧} (h : X ^ k ∣ u - v) :
    X ^ (k + 1) ∣
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v := by
  rw [nodal_map_sub_eq_X_mul_sub_mul, pow_succ']
  exact Dvd.dvd.mul_right (mul_dvd_mul_left X h) _

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_dvd_iterate_sub_iterate (n m : ℕ) :
    X ^ n ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    have e1 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1 + m] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0) := by
      rw [show n + 1 + m = n + m + 1 by omega]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact X_pow_succ_dvd_sub_of_X_pow_dvd W ih

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma vSer_isFixedPt :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W) := by
  ext k
  have h : X ^ k ∣ _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0 := by
    rw [X_pow_dvd_iff]
    intro m hm
    have h2 := X_pow_dvd_iterate_sub_iterate W (m + 1) (k - (m + 1))
    rw [show m + 1 + (k - (m + 1)) = k by omega, X_pow_dvd_iff] at h2
    have h3 := h2 m (Nat.lt_succ_self m)
    rw [map_sub, sub_eq_zero] at h3
    rw [map_sub, sub_eq_zero, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]
    exact h3.symm
  have h2 := X_pow_succ_dvd_sub_of_X_pow_dvd W h
  have e : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k + 1] 0 =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
        ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0) :=
    Function.iterate_succ_apply' _ _ _
  rw [← e, X_pow_dvd_iff] at h2
  have h3 := h2 k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer_eq :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W = X ^ 3 + C W.a₁ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₂ * X ^ 2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₃ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₄ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₆ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 3 := by
  have hv := vSer_isFixedPt W
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer]
  conv_lhs => rw [hv, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step]
  ring

end Expansion

end GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods
