import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AdExt

section Mat
variable {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ}

theorem conj_form (hx : IsUnit x.det) (h : xᴴ * G * x = S) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (x * A * x⁻¹)ᴴ * G * (x * B * x⁻¹) = x⁻¹ᴴ * (Aᴴ * S * B) * x⁻¹ := by
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem conj_mem_lie (hx : IsUnit x.det) (h : xᴴ * G * x = S) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * S + S * Z = 0) : (x * Z * x⁻¹)ᴴ * G + G * (x * Z * x⁻¹) = 0 := by
  have h1 := conj_form hx h Z 1
  have h2 := conj_form hx h 1 Z
  rw [Matrix.mul_one, mul_nonsing_inv _ hx] at h1 h2
  rw [Matrix.mul_one] at h1
  rw [conjTranspose_one, Matrix.one_mul] at h2
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]
  simp

theorem conj_mem_unitary (hx : IsUnit x.det) (h : xᴴ * G * x = S) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * S * A = S) : (x * A * x⁻¹)ᴴ * G * (x * A * x⁻¹) = G := by
  have h2 := conj_form hx h 1 1
  rw [Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one] at h2
  rw [conj_form hx h, hA, ← h2]

theorem diag_unitary (s : Fin n → ℂ) (t : Fin n → ℝ) :
    (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I))ᴴ * diagonal s *
      (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I)) = diagonal s := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext c
  have : star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Pi.star_apply]
  linear_combination s c * this

theorem half_mem_lie (hG : Gᴴ = G) (hd : IsUnit G.det) (W : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G))) = 0 := by
  have e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hd, Matrix.mul_one]
  have e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

theorem conj_eq_of_mem_lie (hd : IsUnit G.det) {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * G + G * W = 0) :
    -(G⁻¹ * Wᴴ * G) = W := by
  rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]

end Mat

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem atTau_spec (R : RealPoints θ V) (ρ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V ρ * g = gramAt D V ρ) : IsAtTau θ V ρ g (atTau θ V ρ g) := by
  have h : ∃ k, IsAtTau θ V ρ g k := by
    obtain ⟨k, hk, h⟩ := R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by
      change _ᴴ * _ * _ = _
      split_ifs with c
      · subst c; exact hg
      · simp
    exact ⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩
  rw [atTau, dif_pos h]
  exact h.choose_spec

def toLie (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) : Frame Ψ V.rank →ₗ[ℝ] LieN V where
  toFun Z := fun ρ => ⟨(1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)),
    half_mem_lie (R.1 ρ).1 (R.1 ρ).2 _⟩
  map_add' Z Z' := funext fun ρ => Subtype.ext (by
    have : mat (Z + Z') (σ ρ) = mat Z (σ ρ) + mat Z' (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) • _ + (1 / 2 : ℂ) • _
    simp only [this, conjAt, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]
    module)
  map_smul' c Z := funext fun ρ => Subtype.ext (by
    have : mat (c • Z) (σ ρ) = c • mat Z (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = c • (1 / 2 : ℂ) • _
    simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, star_trivial]
    module)

theorem toLie_val (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ Z ρ).1 =
    (1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := rfl

theorem toLie_I (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ (Complex.I • Z) ρ).1 =
    (Complex.I / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ - conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := by
  have : mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ) := rfl
  rw [toLie_val]
  simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  module

theorem fderiv_atPlace (R : RealPoints θ V) {φ : GA D V → ℂ} (g : GA D V)
    (hf : DifferentiableAt ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0) (ρ : D.what₂.Tau) (Y : LieAt V ρ) :
    fderiv ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0 (atPlace V ρ Y : LieN V) = Rder θ V ρ Y.1 φ g := by
  rw [Rder_eq R]
  have h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0 := fun Y' => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y'
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm
  exact h2.deriv.symm

theorem mat_unitFr {Ψ : Finset (D.host.E →+* ℂ)} {r : ℕ} (τ τ' : Ψ) (c d : Fin r) :
    mat (unitFr τ c d) τ' = if τ' = τ then Matrix.single c d 1 else 0 := by
  ext a b
  by_cases h : τ' = τ
  · simp [mat, unitFr, h, Matrix.single, eq_comm]
  · simp [mat, unitFr, h]

end GlobalTheory.HolRead.AdExt
