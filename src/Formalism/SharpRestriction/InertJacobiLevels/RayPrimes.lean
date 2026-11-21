import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.FamCore

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

def TNorm {R : Ranks} (H : Host R) (T : ℕ) : Prop :=
  ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}

structure Fits (lb : Bool) (D : D7) {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A)
    (T Lw β : ℕ) (Tstar Gam : ℝ) : Prop where
  host_eq : (⟨D.R, D.host⟩ : Σ R : Ranks, Host R) = ⟨Rt s, hostOf A u0 T Lw⟩
  word : ∀ u : D.what₂.Word, u = D.u₀
  letter : ∀ u l, D.s.letter u l = lb
  eta : ∀ j w, D.what₂.etaJ j w = 0
  Aj_eq : ∀ j w, D.what₂.Aj j w = 0
  T_eq : ∀ u, (D.mem u).A.T = T
  Tstar_eq : ∀ u, (D.mem u).A.Tstar = Tstar
  Gam_eq : ∀ u, (D.mem u).A.GamP = Gam
  Del_eq : (D.s.Del : ℝ) = 1
  hv : ∀ τ (i : Fin (D.R.k - 1)), (D.hc τ).v i = 24 - 4 * ((i : ℕ) : ℚ)
  hu0 : ∀ τ (h : 0 < D.R.k), (D.hc τ).u ⟨0, h⟩ = 113 / 2
  hu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k → (D.hcW u τ).u i = 55 / 2 - 4 * ((i : ℕ) : ℚ)
  hb : ∀ τ (j : Fin D.R.m), (D.hc τ).b j = β + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)
  he : ∀ τ (j : Fin D.R.m), (D.hc τ).e j = β + ((s : ℚ) + 9) + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)

end Formalism.MainNotions.Inhab

end
