import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (descend LeftInv mk measurable_mk)
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.RealInd (IsIrrAdm IsIndModel IndModule Flag groupRep indFun leviOne mats)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar

section Disc

variable {n : ℕ}

def weylDisc (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  resultant x.charpoly (derivative x.charpoly) n (n - 1) / x.det ^ (n - 1)

end Disc

section Cartan

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_ujMat : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val

def IsCartanSub (T : Subgroup (UJ ε)) : Prop := ∃ s, IsRegSS (ujMat ε s) ∧ T = cent s

def IsCartanSystem (𝒯 : Finset (Subgroup (UJ ε))) : Prop :=
  (∀ T ∈ 𝒯, IsCartanSub T) ∧
    ∀ T : Subgroup (UJ ε), IsCartanSub T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T'

def weylOrder {H : Type} [Group H] (T : Subgroup H) : ℕ := T.relIndex (Subgroup.normalizer (T : Set H))

end Cartan

section Char

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def IsAnalyticAt (Θ : UJ ε → ℂ) (s : UJ ε) : Prop :=
  ∃ Φ : (Fin n → Fin n → ℂ) → ℂ, AnalyticAt ℝ Φ (matCoord (ujMat ε) s) ∧ ∀ᶠ g in 𝓝 s, Θ g = Φ (matCoord (ujMat ε) g)

def IsGlobalChar (μ : Measure (UJ ε)) (π : UJ ε →* (V →L[ℂ] V)) (Θ : UJ ε → ℂ) : Prop :=
  IsCharFn (ujMat ε) μ π Θ ∧ ∀ s, IsRegSS (ujMat ε s) → IsAnalyticAt Θ s ∧ ∀ x, Θ (x⁻¹ * s * x) = Θ s

end Char

section Torus

variable {n : ℕ}

def torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) : UJ ε :=
  ⟨⟨diagonal fun a => Complex.exp (θ a * Complex.I), diagonal fun a => Complex.exp (-(θ a * Complex.I)),
    by simp [← Complex.exp_add], by simp [← Complex.exp_add]⟩, by
      change _ᴴ * Jm ε * _ = Jm ε
      simp only [Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext a
      rw [mul_right_comm, Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

def wtVal (μ θ : Fin n → ℝ) : ℂ := Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I)

def weylDenom (θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def compactWeyl (ε : Fin n → Bool) : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun w => ε ∘ w = ε

def halfDim (ε : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a => ε a = true).card * (Finset.univ.filter fun a => ε a = false).card

def dsChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / weylDenom θ

theorem weylDenom_mul (θ : Fin n → ℝ) : weylDenom θ * wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
    ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  have h : ∑ a, ((n : ℝ) - 1) / 2 * θ a = ∑ a, ∑ b ∈ Finset.Ioi a, (θ a + θ b) / 2 := by
    have h1 : ∑ a, ∑ b ∈ Finset.Ioi a, θ b = ∑ b, ∑ _a ∈ Finset.Iio b, θ b :=
      Finset.sum_comm' (by simp)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [weylDenom, wtVal, h]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring

theorem dsChar_eq (ε : Fin n → Bool) {lam : Fin n → ℝ} {m : Fin n → ℤ} (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a)
    (θ : Fin n → ℝ) : dsChar ε lam θ = (-1) ^ halfDim ε *
      (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, Complex.exp (θ a * Complex.I) ^ m (w.symm a)) /
        ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  rw [dsChar, ← weylDenom_mul, ← mul_div_mul_right _ _ (c := wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) (Complex.exp_ne_zero _),
    mul_assoc, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, wtVal, wtVal, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  simp only [← add_mul, Function.comp, hm, ← Complex.exp_int_mul, ← Complex.exp_sum, Complex.ofReal_sum,
    Finset.sum_mul]
  simp [mul_assoc]

end Torus

end GlobalTheory.HCChar

namespace GlobalTheory.Published

open GlobalTheory.HCChar

def CharacterRegularity : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsIrrAdm ε π),
    ∃ Θ, IsGlobalChar μ (groupRep ε h.2.1.1) Θ

def DiscreteSeriesCharacter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)),
    IsHCParam lam → IsDS ε lam σ → ∀ h : IsURepOn (UJset ε) σ, ∃ Θ, IsGlobalChar μ (ujRep h) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

def WeylIntegrationFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯) ∧
    (∀ T : Subgroup (UJ ε), IsCartanSub T → weylOrder T ≠ 0) ∧
    ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (𝒯 : Finset (Subgroup (UJ ε))), IsCartanSystem 𝒯 →
      ∀ dt : ∀ T : Subgroup (UJ ε), Measure T, (∀ T ∈ 𝒯, (dt T).IsHaarMeasure) →
        ∀ F : UJ ε → ℝ≥0∞, Measurable F →
          ∫⁻ g, F g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℝ≥0∞)⁻¹ *
            ∫⁻ t : T, ‖weylDisc (ujMat ε t)‖ₑ * ∫⁻ q, F (q.out⁻¹ * t * q.out) ∂quotMeas T (dt T) μ ∂dt T

def InducedCharacterSupport : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → a ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι → ∀ h : IsCRepOn (UJset ε) ρ, ∃ Θ, IsGlobalChar μ (groupRep ε h) Θ ∧
          ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε W) → Θ g = 0

def HarishChandraCharacters : Prop :=
  CharacterRegularity ∧ DiscreteSeriesCharacter ∧ WeylIntegrationFormula ∧ InducedCharacterSupport

end GlobalTheory.Published
