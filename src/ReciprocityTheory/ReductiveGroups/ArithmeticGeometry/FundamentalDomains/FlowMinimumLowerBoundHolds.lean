import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]

end ReciprocityTheory.ChartRestriction.G.FD
