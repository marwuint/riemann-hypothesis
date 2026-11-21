import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.GramExists
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NormLeInvOfLtOne

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

namespace OrbitCoverLemmas

end OrbitCoverLemmas

namespace OrbitCoverLemmas

def blk {K : Type} [Field K] (lam : K) (k x : Bool) : K :=
  if x = false then (if k = false then 1 else lam) else (if k = false then 2⁻¹ else -lam * 2⁻¹)

theorem blk_gram {K : Type} [Field K] (σ : K →+* K) (lam : K) (h2 : (2 : K) ≠ 0)
    (h : lam * σ lam = -1) (x x' : Bool) :
    ∑ k, blk lam k x * σ (blk lam k x') = if x ≠ x' then 1 else 0 := by
  have s2 : σ 2 = 2 := map_ofNat σ 2
  cases x <;> cases x' <;> simp [blk, map_inv₀, s2]
  · linear_combination h
  · field_simp; linear_combination -h
  · field_simp; linear_combination -h
  · field_simp; linear_combination h

theorem lam_spec {K : Type} [Field K] (σ : K →+* K) (m : ℕ) (hm : 0 < m) (ζ : K)
    (hζ : IsPrimitiveRoot ζ ((2 * m + 1) ^ 2 - 1)) (hσ : σ ζ = ζ ^ (2 * m + 1)) :
    (ζ ^ m) * σ (ζ ^ m) = -1 := by
  have e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2 := by
    have : (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1 := by ring
    omega
  have hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2 := by
    have := hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)
    rwa [e, Nat.mul_div_cancel_left _ (by positivity)] at this
  have := hp.eq_neg_one_of_two_right
  rw [map_pow, hσ, ← this]; ring

theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (h : ‖((2 * m + 1 : ℕ) : K)‖ < 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K)) := by push_cast; ring
  have h1 : ‖(1 : K)‖ < 1 := by
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)
    rw [norm_neg, norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [norm_one] at h1
  exact lt_irrefl _ h1

end OrbitCoverLemmas

theorem gram_matrix_exists : GramExists := by
  intro K _ _ _ l σ hU hζ E _ _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hp, hl2, hnl, -, -⟩ := id hU
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hm : 0 < m := by omega
  have hσζ : σ ζ = ζ ^ (2 * m + 1) := teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one
  have hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * m + 1) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    have e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hζ.pow_eq_one, one_mul]
  have hlam := OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ
  have n2 : ‖(2 : K)‖ = 1 := by
    refine OrbitCoverLemmas.norm_two m ?_
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have nlam : ‖ζ ^ m‖ = 1 := by rw [norm_pow, nζ, one_pow]
  have s2 : σ 2 = 2 := map_ofNat σ 2
  have hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧
      σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x := by
    intro k x
    cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]
  refine ⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hblk _ _
    · simp
  · rintro ⟨b, e⟩ ⟨b', e'⟩
    rw [Fintype.sum_prod_type]
    dsimp only
    by_cases h : e = e'
    · subst h
      have h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) *
          σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) =
          OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b') := by
        intro k
        rw [Finset.sum_eq_single e]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      simp only [h3]
      rw [OrbitCoverLemmas.blk_gram σ _ h2 hlam]
      simp
    · rw [if_neg (fun h' => h h'.2)]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y = e
      · have : ¬ y = e' := fun h' => h (hy ▸ h')
        simp [this]
      · simp [hy]

end Formalism.L2.Th1.D
