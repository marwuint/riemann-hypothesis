import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

theorem complex_span_block_action_stable (lam : ι → DomWeight n) (w : ι → Matrix (Fin n) (Fin n) ℂ)
    {P : MvPolynomial (ι × Fin n × Fin n) ℂ} (hP : P ∈ CSpan lam) : blockAct ℂ w P ∈ CSpan lam := by
  have h1 : CSpan lam ≤ VV ℂ lam := by
    refine (Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    simpa [MvPolynomial.map_id] using hF'
  have h2 : blockAct ℂ w P ∈ VV ℂ lam :=
    (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n w).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ))
      (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)
  simpa [MvPolynomial.map_id] using Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam _ h2

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
