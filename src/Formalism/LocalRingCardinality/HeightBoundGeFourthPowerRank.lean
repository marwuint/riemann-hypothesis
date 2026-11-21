import Formalism.LocalRingCardinality.DataParamsT
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

namespace Formalism.BasicNotions

theorem D7.eight_le_f (D : D7) : 8 ≤ D.R.f := by
  have h : 2 ≤ D.R.e := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) h
  have h5 : 2 ^ D.R.e ≤ D.R.ord := D.R.toFrame.two_pow_le_ord
  unfold Ranks.f Ranks.n
  omega

theorem ParameterChoice'.m_sq_le_k {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.R.m ^ 2 ≤ D.R.k := by
  have h1 : (1 : ℝ) ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have h2 := P.k_ge_m2L
  have h3 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by positivity
  have h4 : (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by nlinarith
  exact_mod_cast h4

def D7.NodeGap (D : D7) (h : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    h ≤ (((D.hcW u τ).b ⟨j + 1, hj⟩ - (D.hcW u τ).b ⟨j, by omega⟩ : ℚ) : ℝ)

theorem D7.NodeGap.mono {D : D7} {h h' : ℝ} (H : D.NodeGap h) (hle : h' ≤ h) : D.NodeGap h' :=
  fun u τ j hj => le_trans hle (H u τ j hj)

theorem ParameterChoice'.nodeGap_ge_heightBound {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.NodeGap (LevelStarExponents.h0 L) := by
  intro u τ j hj
  rw [D.hcW_b u τ]
  exact (P.nodes_gap τ j hj).1

theorem ParameterChoice'.nodeGap_ge_cubic_rank {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    D.NodeGap (4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6) :=
  P.nodeGap_ge_heightBound.mono P.h0_ge.2.2.2.2.1

end Formalism.BasicNotions
