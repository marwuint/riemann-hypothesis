import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormLeOneIffIsIntegral
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

abbrev Q0 (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (Om l) := ⊥

theorem finiteDimensional_Q0_alt : FiniteDimensional ℚ_[l] (Q0 l) := inferInstance

def ofGQ (g : GQ l) : Neutral.B1.GK l (Q0 l) :=
  { g.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 r.2
      change g (r : Om l) = r
      rw [← ha]
      exact g.commutes a }

theorem ofGQ_apply (g : GQ l) (x : Om l) : ofGQ g x = g x := rfl

theorem Kur_eq : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by
  rw [LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩
  · rintro ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩

variable (l) in

def FrobQ : GQ l := (LocalClassField.frobK l (Q0 l)).restrictScalars ℚ_[l]

theorem FrobQ_apply (x : Om l) : FrobQ l x = LocalClassField.frobK l (Q0 l) x := rfl

theorem FrobQ_pow_apply (i : ℕ) (x : Om l) : (FrobQ l ^ i) x = (LocalClassField.frobK l (Q0 l) ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, FrobQ_apply]

section Fin

variable {F : IntermediateField ℚ_[l] (Om l)}

theorem norm_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by
  rw [← Kur_eq] at hx
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx
  obtain ⟨y, hy, h⟩ := LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hy
  exact ⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩

theorem eq_Kn (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) :
    F = LocalClassField.Kn l (Q0 l) (Module.finrank ℚ_[l] F) := by
  refine LocalClassField.eq_Kn_of_norm l (Q0 l) finiteDimensional_Q0_alt bot_le Module.finrank_pos ?_ ?_
  · rw [IntermediateField.finrank_bot, mul_one]
  · intro x hx
    obtain ⟨a, ha⟩ := norm_Kur (hle hx)
    exact ⟨algebraMap ℚ_[l] (Om l) a, IntermediateField.algebraMap_mem _ a,
      ha.trans (PadicAlgCl.norm_extends l a).symm⟩

theorem map_mem (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l) {x : Om l}
    (hx : x ∈ F) : g x ∈ F := by
  rw [eq_Kn hF hle] at hx ⊢
  exact LocalClassField.map_mem_Kn l (Q0 l) _ (ofGQ g) hx

theorem normal_of_le_Kur (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) : Normal ℚ_[l] F := by
  rw [IntermediateField.normal_iff_forall_map_le']
  rintro g _ ⟨x, hx, rfl⟩
  exact map_mem hF hle g hx

theorem pow_fixes_iff (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (i : ℕ) :
    (∀ x ∈ F, (FrobQ l ^ i) x = x) ↔ Module.finrank ℚ_[l] F ∣ i := by
  rw [← LocalClassField.IsFrobOn.pow_fixes_iff l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F))
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) i, ← eq_Kn hF hle]
  simp only [FrobQ_pow_apply]

end Fin

end Formalism.L2.LocGap.Gal
