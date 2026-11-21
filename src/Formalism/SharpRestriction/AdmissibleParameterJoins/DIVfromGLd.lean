import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def LevelPrimeBasicClauses (D : D7) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax

theorem sum_lwP_e_le (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w ∈ S, D.what₂.places.resChar w = p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p := by
  classical
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => mul_nonneg (lw_nonneg v) (Nat.cast_nonneg _))

def LenAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T →
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) =
      product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w)

def LocSpan (D : D7) : Prop :=
  ∀ u w, ∀ y ∈ (D.fm u).S 0 w, InLoc (D.plEq w) ((D.fm u).lat 0).L y

def LevelPrimeSizeBounds (D : D7) (L : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ u w, product_first_zeroth_parts.OverT D u w → ∑ v ∈ product_first_zeroth_parts.VV D u w,
      ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤
    C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b')

end Formalism.MainNotions.J
