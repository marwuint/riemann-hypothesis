import Mathlib

namespace Formalism.GM

open Finset Polynomial

noncomputable def gch (x : ℚ) (k : ℕ) : ℚ := (descPochhammer ℚ k).eval x / (k.factorial : ℚ)

noncomputable def gchPoly (c : ℚ) (k : ℕ) : ℚ[X] :=
  Polynomial.C ((k.factorial : ℚ)⁻¹) * (descPochhammer ℚ k).comp (X + Polynomial.C c)

def GchBasics : Prop :=
  (∀ n k : ℕ, gch (n : ℚ) k = (n.choose k : ℚ)) ∧ (∀ (c x : ℚ) (k : ℕ), (gchPoly c k).eval x = gch (x + c) k)

def DetDegTop : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (a b : Fin n → ℕ),
    (∀ i j, (A i j).natDegree ≤ a i + b j) →
      (A.det).natDegree ≤ ∑ i, a i + ∑ j, b j ∧
      (A.det).coeff (∑ i, a i + ∑ j, b j) = (Matrix.of fun i j => (A i j).coeff (a i + b j)).det

def DetBlockLead : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (D : ℕ) (e : Fin n → ℕ),
    (∀ i, e i ≤ D) → (∀ i j, (A i j).natDegree + max (e i) (e j) ≤ D) →
      (A.det).natDegree ≤ ∑ i, (D - e i) ∧
      (A.det).coeff (∑ i, (D - e i)) =
        (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ∧
      ((Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ≠ 0 →
        (A.det).natDegree = ∑ i, (D - e i) ∧
        (A.det).leadingCoeff = (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det)

noncomputable def tiePoly {m : ℕ} (J : ℕ) (c : ℚ) (B : ℕ → Matrix (Fin m) (Fin m) ℚ) :
    Matrix (Fin m) (Fin m) ℚ[X] :=
  ∑ l ∈ range (J + 1),
    ((-1 : ℚ[X]) ^ l * gchPoly (c - l) (J - l) * Polynomial.C ((gch (J : ℚ) l)⁻¹)) • (B l).map Polynomial.C

def TiePoly : Prop :=
  ∀ (m J : ℕ) (c : ℚ) (B : ℕ → Matrix (Fin m) (Fin m) ℚ), B 0 = 1 →
    (∀ i j, ((tiePoly J c B) i j).natDegree ≤ J) ∧
    (∀ i j, ((tiePoly J c B) i j).coeff J = if i = j then ((J.factorial : ℚ))⁻¹ else 0)

noncomputable def vmin (p : ℕ) {K : Type} [NormedField K] (h : ℕ) (x : K) : ℝ :=
  -Real.logb p (max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))))

def WindowCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (ζ : K) (t₀ : ℤ) (Y₀ h : ℕ),
    ∑ t ∈ Ico t₀ (t₀ + Y₀), vmin p h ((t : K) - ζ) ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1)

def CycleProd : Prop :=
  ∀ (J : ℕ) [NeZero J] (p : ℝ) (Q : Fin J → ℝ) (R : Fin J → ℤ), p ≠ 0 →
    ∏ j, Q (j + 1) * p ^ (R (j + 1) - R j) = ∏ j, Q j

def CoarseSlack : Prop :=
  ∀ (p a Y k Ns Qn be : ℝ) (D₁ L₁ Rj Rn : ℤ),
    1 < p → 0 < a → 0 < Y → 0 < k → 0 < Ns → 0 < Qn →
    be ≤ 4 * a * p ^ (-D₁ - L₁ - Rj) →
    a / (4 * Y * k ^ 2 * Ns * p ^ D₁ * Qn) < p ^ (Rn + 1) →
    64 * p * k ^ 2 * Ns * Y ^ 2 ≤ p ^ L₁ →
    be / (Qn * p ^ (Rn - Rj)) ≤ 16 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ∧
      16 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ≤ 1 / (4 * Y)

def SatSub : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] (n : ℕ)
    (L : Submodule R (Fin n → R)),
    ∃ M : Submodule R (Fin n → R), M ≤ L ∧
      Module.finrank R M =
        Module.finrank (IsLocalRing.ResidueField R)
          (Submodule.span (IsLocalRing.ResidueField R)
            ((fun v : Fin n → R => fun i => IsLocalRing.residue R (v i)) '' (L : Set (Fin n → R)))) ∧
      ∀ (a : R) (x : Fin n → R), a ≠ 0 → a • x ∈ M → x ∈ M

def CoarseDiv : Prop :=
  ∀ (p m n i : ℕ), p.Prime → 1 ≤ i → i ≤ p ^ m * n →
    m ≤ padicValNat p ((p ^ m * n).choose i) + padicValNat p i

def MeanBad : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : Finset ℤ) (ntop : ℤ) (mult n₀ : ι → ℝ) (bad y : ι → ℤ → ℝ) (CK : ℝ),
    N.Nonempty → (∀ w, 0 ≤ mult w) → (∀ w n, n ∈ N → 0 ≤ bad w n) →
    (∀ w n, n ∈ N → 0 ≤ y w n ∧ y w n ≤ y w ntop) →
    (∀ w, (∑ n ∈ N, bad w n) / N.card ≤ CK * n₀ w) →
    (∑ n ∈ N, ∑ w, mult w * bad w n * y w n) / N.card ≤ CK * ∑ w, mult w * n₀ w * y w ntop

end Formalism.GM
