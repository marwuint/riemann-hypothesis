import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Size GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped ENNReal ComplexOrder

namespace GlobalTheory.ChainFr.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_sign_frame {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hu : IsUnit G.det) :
    ∃ (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsUnit A ∧ Aᴴ * Formalism.REAL.Jm ε * A = G := by
  classical
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := by
    intro i h0
    apply hu.ne_zero
    rw [hG.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
  set U : Matrix (Fin n) (Fin n) ℂ := (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : G = U * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hG.spectral_theorem]
    simp [hU, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]
  let d : Fin n → ℂ := fun i => ((Real.sqrt |hG.eigenvalues i| : ℝ) : ℂ)
  refine ⟨fun i => decide (0 < hG.eigenvalues i), diagonal d * Uᴴ, ?_, ?_⟩
  · refine IsUnit.mul ?_ ?_
    · rw [isUnit_diagonal, Pi.isUnit_iff]
      intro i
      simp [d, hne i]
    · have : Uᴴ * U = 1 := by
        rw [hU, ← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
      exact IsUnit.of_mul_eq_one _ this
  · have key : (diagonal d)ᴴ * Formalism.REAL.Jm (fun i => decide (0 < hG.eigenvalues i)) * diagonal d =
        diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      have hs : d i * d i = ((|hG.eigenvalues i| : ℝ) : ℂ) := by
        simp only [d]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
      have hst : star d i = d i := by simp [d]
      rw [hst]
      by_cases h : 0 < hG.eigenvalues i
      · simp only [h, decide_true, if_true, mul_one, hs, abs_of_pos h]
      · simp only [h, decide_false, Bool.false_eq_true, if_false, mul_neg, mul_one, neg_mul, hs,
          abs_of_nonpos (not_lt.1 h)]
        simp
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    conv_rhs => rw [hsp, ← key]
    simp only [Matrix.mul_assoc]

theorem nonempty_fr (V : HSp D) : Nonempty (Fr V) := by
  choose ε A hA hG using fun τ => exists_sign_frame (G := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, A, hA, hG⟩⟩

theorem isCartanInv_cart {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have hd := (isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJc := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hJJ : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Formalism.REAL.Jm (A.ε τ) * (Formalism.REAL.Jm (A.ε τ) * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h1 : A.fr τ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
    simp only [Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have h2 : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ, Matrix.mul_assoc, h1, Matrix.mul_assoc, hJJ]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ, Matrix.nonsing_inv_mul _ hd]
  · rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_mul, hJc, A.fr_gram]
  · rw [h2]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (A.fr_unit τ))

theorem exists_vac {V W : HSp D} (A : Fr V) (B : Fr W) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) :
    ∃ f, f ≠ 0 ∧ IsVacF ψ θ A B f ∧ ptF ψ θ A B f 1 = f ∧
      ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ fockSpan ψ θ A B U := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ (isCartanInv_cart A) (isCartanInv_cart B) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h : IsVacF ψ θ A B f := ⟨by simpa using (hf 1).1, by simpa using (hf 1).2.2⟩
  have e : ptF ψ θ A B f 1 = f := by
    have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    unfold ptF pureTensorO pureTensorL
    rw [h1, Module.Basis.constr_basis]
    simp [opPow]
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 h.1
  exact ⟨f, f0, h, e, U, hU, Submodule.subset_span ⟨f, 1, h, hl, e.symm⟩⟩

end GlobalTheory.ChainFr.Model

end
