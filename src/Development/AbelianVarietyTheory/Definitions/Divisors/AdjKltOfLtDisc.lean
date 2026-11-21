import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

theorem lt_disc (h : AdjKlt c n T S η φ) {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q}
    {E : Place c} (hT : T ≤ Q)
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (hE : E.IsPrimeOf Q)
    (ht : S.ord (t : K) = 1) (hu : E.ord (u : K) = 1)
    (h0 : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) :
    -1 < E.disc η φ :=
  h.2.2 Q hQ t u E hT hm hd hS hE ht hu h0

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

end GlobalTheory.FieldPair
