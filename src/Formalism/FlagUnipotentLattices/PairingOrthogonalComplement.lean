import Mathlib
import Formalism.SobolevGaussianKernels.StatementEI

namespace Formalism.HermitianLatticeCounting.S4

open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)

def ValuationProductBound : Prop :=
  ∀ (B : Type) [Fintype B] (s : B → ℕ) (vh ve vt : B → ℝ) (q A : ℝ) (r : ℕ),
    1 ≤ q → (∀ b, 1 ≤ s b ∧ s b ≤ r + 1) → (∀ b, 0 ≤ vh b) → (∀ b, 0 ≤ ve b) →
    (∀ b, (s b : ℝ) * vt b = ve b - vh b) → ∑ b, vh b ≤ A → ∑ b, ve b ≤ A →
    ∏ b, q ^ (2 * (s b : ℝ) * vh b) ≤ (q ^ A) ^ (2 * ((r : ℝ) + 1)) ∧
    ∏ b, q ^ (vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2)) ≤ (q ^ A) ^ (((r : ℝ) + 1) / 2)

def LocalDensityShareBound : Prop :=
  ∀ (Ov : Type) [Fintype Ov] (dens dl : Ov → ℝ) (κ be disc tot : ℝ) (k r : ℕ),
    1 ≤ k → 0 ≤ κ → 1 ≤ be → (Fintype.card Ov : ℝ) ≤ disc ^ (2 * r + 2) →
    (∀ M, dens M = κ * ((be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹) * dl M) →
    (∀ M, dl M ≤ 2) → κ / 2 ≤ tot →
    ∑ M, dens M ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot

structure Unram (o O : Type*) [CommRing o] [CommRing O] [StarRing O] [Algebra o O] : Prop where
  star_o : ∀ c : o, star (algebraMap o O c) = algebraMap o O c
  free : Module.Free o O
  rank2 : Module.finrank o O = 2
  tr_onto : ∀ c : o, ∃ s : O, s + star s = algebraMap o O c
  tr_perfect : ∀ φ : O →ₗ[o] o, ∃ b : O, ∀ a : O,
    algebraMap o O (φ a) = a * star b + star (a * star b)

def WeightedCS : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : Type) [SeminormedAddCommGroup V] (v : ι → V) (W : ι → ℝ),
    (∀ i, 0 < W i) → ‖∑ i, v i‖ ^ 2 ≤ (∑ i, (W i)⁻¹) * ∑ i, W i * ‖v i‖ ^ 2

def OmCount : Prop :=
  ∀ (P : Type) (Om : Finset P) (H : P → ℝ), (∀ p ∈ Om, 2 ≤ H p) → (2 : ℝ) ^ Om.card ≤ ∏ p ∈ Om, H p

def Step4 : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (Om : Finset P) (D : P → Type) [∀ p, Fintype (D p)]
    (w : ∀ p, D p → ℝ) (aN aZ : ∀ p, D p → ℂ) (H nn ngen : P → ℝ) (q : P → ℕ) (c κ : ℕ),
    (∀ p d, 0 ≤ w p d) → (∀ p, 1 ≤ H p) → (∀ p, 2 ≤ q p) → (∀ p, 0 ≤ nn p) →
    (∀ p ∈ Om, ∑ d, w p d * ‖aN p d‖ ^ 2 ≤ H p ^ c * ((q p : ℝ) ^ κ)⁻¹ * nn p) →
    (∀ p, ∑ d, w p d * ‖aZ p d‖ ^ 2 ≤ H p ^ c * nn p) →
    (∀ p, nn p ≤ H p ^ c * ngen p) →
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
            ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ (4 : ℝ) ^ Om.card * (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p

end Formalism.HermitianLatticeCounting.S4
