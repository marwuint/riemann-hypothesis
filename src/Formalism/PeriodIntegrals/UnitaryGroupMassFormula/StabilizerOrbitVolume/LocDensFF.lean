import Mathlib

noncomputable section

namespace PI.VolStabSW

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

end PI.VolStabSW
