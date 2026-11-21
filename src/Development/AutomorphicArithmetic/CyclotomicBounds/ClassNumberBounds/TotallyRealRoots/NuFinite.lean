import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFormula
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nf_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nf_mem_princ {a s : ℕ} (h : s ≤ a) {u : ℤ_[l]ˣ}
    (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) : u ∈ princ l s := by
  rw [mem_princ, hu]
  exact pow_dvd_pow _ h

private theorem nf_emult {a : ℕ} {u : ℤ_[l]ˣ} (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) :
    emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
  rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (nf_mem_princ (by omega) hu)
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by
    rw [hu]
    exact pow_dvd_pow _ (by omega)
  have := nf_nu_le hm tr
  rw [emultiplicity_pow_sub_one_sq h1, nf_emult hu,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) this

end KStar.TotallyRealRoots
