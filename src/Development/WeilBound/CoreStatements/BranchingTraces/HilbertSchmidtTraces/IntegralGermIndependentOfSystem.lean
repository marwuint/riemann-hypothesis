import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

def IntegralGermIndependentOfSystem : Prop := ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2

def EmbSt : Prop := (∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → ∃ ι : UJ ε' →* UJ ε, (∀ h, umat (ι h) = emb e (um h)) ∧ IsStdStab ε ε' ι (Pi.single (zi e) 1) ∧ ∀ h : Matrix (Fin n) (Fin n) ℂ, incl e * h * (incl e)ᴴ + vecMulVec (Pi.single (zi e) (1 : ℂ)) (star (Pi.single (zi e) (1 : ℂ) : Fin (n + 1) → ℂ)) = emb e h) ∧ (∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m), nsq (g *ᵥ Pi.single j 1) = colSq g j) ∧ (∀ {m : ℕ} (ε : Fin m → Bool) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), IsURepOn (UJset ε) π → IsU (onU ε π)) ∧ ∀ {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)), μ.IsHaarMeasure → IsHCParam lam → IsDS ε lam π → μ.IsMulRightInvariant ∧ (∃ d, IsFdeg μ π d ∧ IsFd μ (onU ε π) d) ∧ ∃ v ∈ lowKSub ε lam π, ‖v‖ = 1

theorem num_C {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hx : 3 ≤ x) (hnx : (n : ℝ) ≤ x) :
    Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) ≤
      x ^ (30 * (n + 1) ^ 2) := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ x := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx
  have e1 : Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      (n : ℝ) ^ (6 * (n + 1) ^ 2) * Real.exp 1 ^ (12 * (n + 1) ^ 2) := by
    rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log (pow_pos h0 (6 * (n + 1) ^ 2)), Real.log_pow]
    push_cast
    rw [mul_one]
  rw [e1, show 30 * (n + 1) ^ 2 = 6 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 by ring, pow_add x, pow_add x]
  gcongr

theorem num_D {n : ℕ} {x : ℝ} (hx : 16 ≤ x) (hnx : (n : ℝ) ≤ x) :
    (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (2 * (16 * (n : ℝ) ^ 2) ^ (2 * n ^ 2)) ≤ x ^ (67 * (n + 1) ^ 2) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : 16 * (n : ℝ) ^ 2 ≤ x ^ 3 := by
    rw [pow_succ' x 2]; gcongr
  calc _ ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (x * (x ^ 3) ^ (2 * n ^ 2)) := by gcongr; linarith
    _ = x ^ (60 * (n + 1) ^ 2 + 1 + 6 * n ^ 2) := by rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by
      have a1 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have a2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)

theorem num_Y {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : 9 ≤ x) (hnx : (N : ℝ) ≤ x) :
    64 * (N : ℝ) * ((N : ℝ) + 2 * x ^ (8 * N)) ^ 2 ≤ x ^ (20 * N) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : (N : ℝ) ≤ x ^ (8 * N) := hnx.trans (le_self_pow₀ h1 (by omega))
  calc _ ≤ x ^ 2 * x * (3 * x ^ (8 * N)) ^ 2 := by gcongr <;> nlinarith
    _ = 9 * x ^ (16 * N + 3) := by ring
    _ ≤ x * x ^ (16 * N + 3) := by gcongr
    _ = x ^ (16 * N + 4) := by ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

theorem num_V {N : ℕ} {B x : ℝ} (hN : 3 ≤ N) (hB : 2 ≤ B) (hx : x = 8 * N * B) :
    (4 * N * (Real.sqrt N + 1) * x ^ (10 * N) / ((100 * N * (B + 1)) ^ 2)⁻¹) ^ (2 * N ^ 2) ≤ x ^ (24 * N ^ 3) := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 25 ≤ x := by rw [hx]; nlinarith
  have a1 : 4 * (N : ℝ) ≤ x := by rw [hx]; nlinarith
  have a2 : Real.sqrt N + 1 ≤ x := by
    have : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    linarith
  have a3 : 100 * N * (B + 1) ≤ x ^ 2 := by
    have : 100 * N * (B + 1) ≤ 25 * x := by rw [hx]; nlinarith
    nlinarith
  rw [div_inv_eq_mul]
  calc _ ≤ (x * x * x ^ (10 * N) * (x ^ 2) ^ 2) ^ (2 * N ^ 2) := by gcongr
    _ = x ^ ((10 * N + 6) * (2 * N ^ 2)) := by rw [pow_mul x (10 * N + 6)]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.mul_le_mul_right (N ^ 2) hN])

end PositivityTheory.UnitaryDecomposition.X4
