import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.S

def FdegUniq (R : Ranks) (h : HCParam R) : Prop :=
  ∃ d0 : ℝ, 0 < d0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (V →L[ℂ] V)) (d : ℝ),
    IsDS (epsSH R) (lamSH R h) σ →
    IsFdeg ((CD.cdScaleOf CD.cdHaar _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = d0

variable {R : Ranks} (H : Host R)

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

end Formalism.BasicNotions.Examples₂
