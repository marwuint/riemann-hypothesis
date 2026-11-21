import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompMulLeftXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCreationOperatorsCommuteOfCcr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergAnnihilationCreationCommutatorEqDelta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFamilyExpandCreationAnnihilation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem polEval_X {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) (i : ι) (p : MvPolynomial ι ℂ) :
    polEval m hm f₀ (X i * p) = m i (polEval m hm f₀ p) := by
  simp [polEval, Module.End.mul_apply]

theorem polEval_one {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) : polEval m hm f₀ 1 = f₀ := by
  simp [polEval]

theorem atPl_linear {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial Λ ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : W, MvPolynomial Λ ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := ⟨(PiTensorProduct.mapMultilinear ℂ (fun _ : W => MvPolynomial Λ ℂ) (fun _ : W => MvPolynomial Λ ℂ)).toLinearMap
      (fun _ => LinearMap.id) w, fun A => by
    simp [GlobalTheory.RealLift.atPl]⟩

theorem fock_map_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hccr f₀ hf₀ hvac

  have hm : ∀ i j, fockM H i * fockM H j = fockM H j * fockM H i := _root_.GlobalTheory.CCRFock.fockM_comm H hadd hsmul hccr
  have hcr := _root_.GlobalTheory.CCRFock.CommDM.fockD_fockM_comm H hadd hsmul hccr

  have hd0 : ∀ j, fockD H j f₀ = 0 := by
    rintro ⟨w, a, b⟩
    have h := hvac w a b
    simp only [fockD, unitAt, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply]
    rw [h, smul_zero, neg_zero]
  have hpd := _root_.GlobalTheory.CCRFock.polEval_pderiv (fockM H) (fockD H) hm f₀ hcr hd0
  have hinj0 : Function.Injective (polEval (fockM H) hm f₀) :=
    GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero _ (fockD H) hpd (by rw [polEval_one]; exact hf₀)
  refine ⟨polEval (fockM H) hm f₀ ∘ₗ polMap W (Ix P Q × Ix R S), hinj0.comp (GlobalTheory.T.tensorPolynomialsToProductVariables_injective W _), ?_⟩

  have hX : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T)) =
      fockM H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h, polEval_X]
  have hD : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (MvPolynomial.pderiv l).toLinearMap T)) =
      fockD H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe] at h
    rw [h, hpd]

  choose L hL using fun w : W => atPl_linear (Λ := Ix P Q × Ix R S) w
  intro c T
  have hsum : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w (heisOp (c w)) =
      ∑ l : Ix P Q × Ix R S, ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefM (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (LinearMap.mulLeft ℂ (MvPolynomial.X l)) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefD (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (MvPolynomial.pderiv l).toLinearMap) := by
    intro w
    clear hX hD hpd hinj0 hcr hm hd0 hvac hccr hsmul hadd hf₀
    rw [← hL w (heisOp (c w)), _root_.GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv (c w), map_sum]
    simp only [map_add, map_smul]
    simp only [hL]
  rw [_root_.GlobalTheory.CCRFock.heis_expand H hadd hsmul c]
  simp only [GlobalTheory.RealLift.sumPl, hsum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_sum, map_add, map_smul, hX, hD]
  conv_rhs => rw [Fintype.sum_prod_type]

end GlobalTheory.CCRFock
