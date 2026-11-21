import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsF

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def redK : OK p K →+* resK p K :=
  (resMap p K).codRestrict (resK p K) fun x => (mem_resK_iff p K _).2 ⟨toObar p K x, (x : K).2, rfl⟩

theorem redK_surjective : Function.Surjective (redK p K) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff p K c).1 hc
  exact ⟨⟨⟨x, hx⟩, x.2⟩, Subtype.ext rfl⟩

variable {K}

def gradFun (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) : OK p K :=
  ⟨(((x : Kˣ) : K) - 1) / (π : K) ^ i, by
    rw [mem_OK_iff]
    show ‖((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one (pow_pos (norm_units_pos π) i), norm_pow_uniformiser p K hK hπ i]
    exact x.2.2⟩

theorem gradFun_val (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) :
    ((gradFun p hK hπ i x : K) : PadicAlgCl p) =
      ((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i := rfl

variable (K)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
