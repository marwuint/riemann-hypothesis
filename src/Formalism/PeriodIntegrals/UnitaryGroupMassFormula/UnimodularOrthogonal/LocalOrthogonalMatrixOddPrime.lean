import Mathlib

noncomputable section

namespace PI.UnimodularOrthogonalQuadratic.Loc

open Matrix

section Star

variable {S : Type} [CommRing S] [StarRing S]

structure LocHyp (S : Type) [CommRing S] [StarRing S] : Prop where
  two : IsUnit (2 : S)
  add : ∀ x y : S, star x = x → star y = y → ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y)
  norm : ∀ x : S, star x = x → IsUnit x → ∃ u, u * star u = x

def q {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (v : Fin n → S) : S :=
  ∑ l, (∑ k, v k * H k l) * star (v l)

def elim {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (-A i.succ 0) (Pi.single i 1 : Fin n → S) : Fin (n + 1) → S))

def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (0 : S) (P i) : Fin (n + 1) → S))

end Star

end PI.UnimodularOrthogonalQuadratic.Loc

namespace PI.UnimodularOrthogonalQuadratic

end PI.UnimodularOrthogonalQuadratic
