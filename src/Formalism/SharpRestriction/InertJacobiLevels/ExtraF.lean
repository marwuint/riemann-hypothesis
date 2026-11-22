import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero
import Formalism.LocalRingCardinality.DataParams

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section

variable {R : Ranks} (H : Host R) (hc : Tau2 R → HCParam R) (etaF : ℝ) (Dn : ℕ) (hDel : (0 : ℚ) < (Dn : ℚ))
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * (Dn : ℚ))
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (hu : ∀ τ, FdegUniq R (hc τ))
  (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

end

end Formalism.MainNotions.Inhab

end
