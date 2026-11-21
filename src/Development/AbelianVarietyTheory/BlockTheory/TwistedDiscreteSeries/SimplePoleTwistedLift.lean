import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
