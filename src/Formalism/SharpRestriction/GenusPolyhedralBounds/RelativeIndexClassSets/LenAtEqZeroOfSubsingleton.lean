import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem rho_eq_zero_of_ge {j : ℕ} (hj : D.R.m ≤ j) : WeightFamilies.rho D j = 0 := by
  unfold WeightFamilies.rho Ranks.sigW
  exact Nat.sub_eq_zero_of_le hj

theorem not_killed_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (cu : B.Cu j)
    (χ : WeightFamilies.ExpoSet D (B.Xc j cu)) : ¬ WeightFamilies.Killed B CR T c cu χ := by
  rintro ⟨xi, -, hne, -⟩
  apply hne
  funext i
  exact absurd (hρ ▸ i.2 : i.1 < 0) (Nat.not_lt_zero _)

theorem MggK_eq_top_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.MggK B CR T c j ka = ⊤ := by
  unfold WeightFamilies.MggK
  simp only [iInf_eq_top]
  intro cu χ hk
  exact absurd hk (not_killed_of_rho hρ CR T c cu χ)

theorem MggIn_eq_top_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.MggIn B CR T c j ka = ⊤ := by
  unfold WeightFamilies.MggIn
  rw [MggK_eq_top_of_rho hρ]
  rfl

theorem Qm_subsingleton_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    Subsingleton (WeightFamilies.Qm B CR T c j ka) :=
  Submodule.Quotient.subsingleton_iff.2 (MggIn_eq_top_of_rho hρ CR T c ka)

theorem rhoP_eq_zero_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.rhoP B CR T c j ka = 0 := by
  have := Qm_subsingleton_of_rho (B := B) hρ CR T c ka
  unfold WeightFamilies.rhoP
  exact Module.finrank_zero_of_subsingleton

theorem lenAt_eq_zero_of_subsingleton (la : HeightOneSpectrum (𝓞 B.KO)) (N : Type) [AddCommGroup N] [Module (𝓞 B.KO) N]
    [Subsingleton N] : WeightFamilies.lenAt B la N = 0 := by
  unfold WeightFamilies.lenAt
  rw [Module.length_eq_zero_iff]
  infer_instance

theorem lenAt_Qm_eq_zero_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : Submodule (𝓞 B.KO) (WeightFamilies.Qm B CR T c j ka)) :
    WeightFamilies.lenAt B la (WeightFamilies.Qm B CR T c j ka ⧸ N) = 0 := by
  have := Qm_subsingleton_of_rho (B := B) hρ CR T c ka
  exact lenAt_eq_zero_of_subsingleton la _

def lenQ {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : ℝ :=
  ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
    (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ)

theorem lenQ_of_ge {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hj : D.R.m ≤ j) (CRm : ℝ)
    (T : ℕ) (c : ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) : lenQ G CRm T c la = 0 := by
  unfold lenQ
  rw [lenAt_Qm_eq_zero_of_rho (rho_eq_zero_of_ge hj)]
  simp

theorem rLa_tsum_split {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF}
    (Qf : ∀ la, LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (hI : Summable (fun la => ((Qf la).Ila.toNat : ℝ) * X.lN la))
    (hN : j < D.R.m → Summable (fun la => (Qf la).Net * X.lN la))
    (hC : Summable (fun la => (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la))
    (hQ : Summable (fun la => lenQ G CRm T c la * X.lN la)) :
    Summable (fun la => rLa (Qf la) CRm T c * X.lN la) ∧
    ∑' la, rLa (Qf la) CRm T c * X.lN la =
      (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * ∑' la, (Qf la).Net * X.lN la else 0)) +
      (∑' la, (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) +
      ∑' la, lenQ G CRm T c la * X.lN la := by
  by_cases hj : j < D.R.m
  · have e : (fun la => rLa (Qf la) CRm T c * X.lN la) = fun la =>
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (((Qf la).Ila.toNat : ℝ) * X.lN la) +
          (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((T : ℝ) * (max 0 c / (2 * (G.iet : ℝ)))) *
            ((Qf la).Net * X.lN la) +
          (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la + lenQ G CRm T c la * X.lN la := by
      funext la
      unfold rLa lenQ
      rw [if_pos hj]
      ring
    have h := (((hI.hasSum.mul_left (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ)).add
      ((hN hj).hasSum.mul_left ((Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) *
        ((T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))))))).add hC.hasSum).add hQ.hasSum
    rw [e]
    refine ⟨h.summable, h.tsum_eq.trans ?_⟩
    rw [if_pos hj]
    ring
  · have e : (fun la => rLa (Qf la) CRm T c * X.lN la) = fun la =>
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (((Qf la).Ila.toNat : ℝ) * X.lN la) +
          (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la + lenQ G CRm T c la * X.lN la := by
      funext la
      unfold rLa lenQ
      rw [if_neg hj]
      ring
    have h := ((hI.hasSum.mul_left (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ)).add hC.hasSum).add hQ.hasSum
    rw [e]
    refine ⟨h.summable, h.tsum_eq.trans ?_⟩
    rw [if_neg hj]
    ring

theorem lenQ_tsum_of_ge {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hj : D.R.m ≤ j)
    (CRm : ℝ) (T : ℕ) (c : ℝ) :
    Summable (fun la => lenQ G CRm T c la * X.lN la) ∧ ∑' la, lenQ G CRm T c la * X.lN la = 0 := by
  have e : (fun la => lenQ G CRm T c la * X.lN la) = fun _ => (0 : ℝ) := by
    funext la
    rw [lenQ_of_ge G hj, zero_mul]
  rw [e]
  exact ⟨summable_zero, tsum_zero⟩

theorem ka_eq_addL {j : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hn : wL.n = nW)
    (hk : ka.n = nP + T * nW) : ka = addL wF wL T := by
  obtain ⟨h1, h2, h3⟩ := hF
  apply Formalism.MainNotions.Gaps.SizeBoundsAlt.weight_ext
  · funext τ i
    have := h2 τ i
    simp only [addL, wadd, wsmul]
    zify
    linarith
  · funext τ i
    have := h3 τ i
    simp only [addL, wadd, wsmul]
    zify
    linarith
  · simp only [addL, wadd, wsmul]
    rw [h1, hn, hk]

theorem ka_eq_addL_of_setC {j : ℕ} {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j}
    {T nP nW : ℕ} {h0 : ℝ} (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : ka = addL wF wL T := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -⟩ := hC
  exact ka_eq_addL hIF hIL.1 (hk.trans hV)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
