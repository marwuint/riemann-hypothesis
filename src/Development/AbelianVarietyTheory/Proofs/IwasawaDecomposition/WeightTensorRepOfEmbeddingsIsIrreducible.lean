import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightActionMatrixCoeffPolynomialInEntries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryExtensionOfCmTypeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceStableEqBotOrTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.AlgWtF.tenRepF_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM
  have hstab : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ γ : GQ L n, ∀ w ∈ W, GlobalTheory.AlgWtF.tenRepF emb lam γ w ∈ W) →
      ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W := by
    intro W hW g w hw
    have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ w ∈ W,
        Formalism.L2.DIV.rhoK lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w ∈ W := by
      intro γ₀ hγ₀ w hw
      obtain ⟨γ, rfl⟩ := _root_.GlobalTheory.AlgWtF.ratHom_surjective L n γ₀ hγ₀
      exact hW γ w hw
    by_contra hnot
    have hx : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) ∉
        W.map (Formalism.L2.DIV.VV K lam).subtype := by
      rintro ⟨y, hy, hyx⟩
      exact hnot (by rw [show Formalism.L2.DIV.rhoK lam g w = y from Subtype.ext hyx.symm]; exact hy)
    obtain ⟨ψ, hψx, hψW⟩ := Submodule.exists_le_ker_of_notMem hx
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.ActPolyCoeff.polyAction_coeff_poly K ι n lam (w : Formalism.L2.DIV.Pol K ι n) ψ
    let f : (ι ⊕ ι) × Fin n × Fin n → (L →+* K) × Fin n × Fin n :=
      fun v => (Sum.elim emb (fun τ => (emb τ).comp (IsCMField.complexConj L : L →+* L)) v.1, v.2)
    have hzero := _root_.GlobalTheory.UnitaryDense.unitary_points_dense L n K (MvPolynomial.rename f P) ?_
    · obtain ⟨B, hBc, hBe⟩ := _root_.GlobalTheory.cmType_family_extend L n ι K emb hCM g
      have h0 := hzero B hBc
      rw [MvPolynomial.eval_rename] at h0
      apply hψx
      have h1 : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) =
          Formalism.L2.DIV.actP lam g w := rfl
      rw [h1, hP g, ← h0]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, hBe]
      · simp only [f, Function.comp_apply, Sum.elim_inr]
        rw [hBc (emb τ), hBe τ]
        rfl
    · intro γ₀ hγ₀
      rw [MvPolynomial.eval_rename]
      have h2 := hrat γ₀ hγ₀ w hw
      have h3 : ψ (Formalism.L2.DIV.actP lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w) = 0 :=
        hψW ⟨_, h2, rfl⟩
      rw [hP] at h3
      rw [← h3]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, GlobalTheory.AlgWtF.embGLF]
      · have hinv : (((γ₀⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) =
            ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
          Units.inv_eq_of_mul_eq_one_right hγ₀
        simp only [f, Function.comp_apply, Sum.elim_inr, GlobalTheory.AlgWtF.embGLF, MonoidHom.pi_apply, ← map_inv,
          Matrix.GeneralLinearGroup.map_apply, hinv, ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply,
          RingHom.comp_apply]
  have hsimple : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    _root_.GlobalTheory.TensorIrr.eq_bot_or_eq_top K ι n lam (fun τ => _root_.GlobalTheory.NablaDensity.endo_eq_sum_sqAct K n (lam τ) (_root_.GlobalTheory.AlcZero.nablaSq_simple_charZero K n (lam τ)))
  haveI hnt : Nontrivial (Formalism.L2.DIV.VV K lam) := _root_.GlobalTheory.CoeffSpace.nontrivial_VV K ι n lam
  haveI : Nontrivial (Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, hx⟩ := exists_ne (0 : Formalism.L2.DIV.VV K lam)
    have hxt : x ∈ (⊤ : Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)).toSubmodule := trivial
    rw [← h'] at hxt
    exact hx hxt
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases hsimple W.toSubmodule (hstab W.toSubmodule (fun γ w hw => W.apply_mem_toSubmodule γ hw)) with h | h
  · left; exact Subrepresentation.ext h
  · right; exact Subrepresentation.ext h
