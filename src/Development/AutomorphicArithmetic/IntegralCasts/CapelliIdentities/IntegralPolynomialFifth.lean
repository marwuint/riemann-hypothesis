import Mathlib

namespace UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl

noncomputable def IsIntP {p : ℕ} [inst : Fact p.Prime] : ℂ_[p] → Prop :=
  fun x => ‖x‖ ≤ 1

theorem aux2 {p : ℕ} [inst : Fact p.Prime] :
    IsTopologicalDivisionRing (PadicAlgCl p) :=
  Valued.isTopologicalDivisionRing

theorem aux3 {p : ℕ} [inst : Fact p.Prime] :
    let n := PadicAlgCl.normedField p
    @CompletableTopField (PadicAlgCl p) n.toField
      n.toNormedCommRing.toSeminormedCommRing.toSeminormedRing.toPseudoMetricSpace.toUniformSpace :=
  NormedField.instCompletableTopField

theorem aux4 {p : ℕ} [inst : Fact p.Prime] :
    IsUniformAddGroup (PadicAlgCl p) :=
  Valued.toIsUniformAddGroup

noncomputable def IntegralMv.{u_1} {σ : Type u_1} {p : ℕ} [inst : Fact p.Prime]
    : MvPowerSeries σ ℂ_[p] → Prop :=
  fun F =>
    letI := aux2 (p := p)
    letI := aux3 (p := p)
    letI := aux4 (p := p)
    ∀ n : σ →₀ ℕ, IsIntP (MvPowerSeries.coeff n F)

theorem intMv_X.{u_1} {p : ℕ} [inst : Fact p.Prime] {σ : Type u_1} (i : σ) :
    IntegralMv (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  classical
  change ‖(MvPowerSeries.coeff n (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) : ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one

end UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl
