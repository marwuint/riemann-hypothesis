import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem exists_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, ∃ b' ∈ Bor X.Ψ r,
      lact γ x = rmul x1 b ∧ x1 = lact γ (rmul x b') := by
  obtain ⟨x1, ho, b, hb, h⟩ := ortho_holds r X (lact γ x) (OntoS.dom_lact X hγ hx)
  refine ⟨x1, ho, b, hb, ExtFPf.invF X b, ExtFPf.invF_mem X hb, h, ?_⟩
  rw [FundSetPf.lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]

theorem sec_ne_zero {r : ℕ} (X : Data E r) {L : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : X.IsSec L w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (h : w x ≠ 0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : w (lact γ (rmul x b)) ≠ 0 := by
  rw [hw.2.2 γ hγ _ (OntoS.dom_rmul X hx hb), hw.2.1 x hx b hb]
  exact mul_ne_zero (chi_ne_zero X L hγ) (mul_ne_zero (OntoE.bchar_ne X L hb) h)

end GlobalTheory.KronAssembly
