import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.FiniteDimensionalQ0

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_maxUnramified (K : FinExt l) : K0 K ≤ MaximalUnramifiedExtension l := inf_le_right

instance finiteDimensional_unramified_subfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

instance normal_unramified_subfield (K : FinExt l) : Normal ℚ_[l] ↥(K0 K) :=
  normal_of_le_Kur (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K)

instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩

def σE (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := (FrobQ l).restrictNormal ↥(K0 K)

def σ (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) := (σE K : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

theorem σ_apply (K : FinExt l) (x : ↥(K0 K)) : σ K x = σE K x := rfl

theorem σE_pow_coe (K : FinExt l) (i : ℕ) (x : ↥(K0 K)) :
    (((σE K ^ i) x : ↥(K0 K)) : Om l) = (FrobQ l ^ i) (x : Om l) := by
  have h : σE K ^ i = (FrobQ l ^ i).restrictNormal ↥(K0 K) :=
    (map_pow (AlgEquiv.restrictNormalHom (K₁ := Om l) ↥(K0 K)) (FrobQ l) i).symm
  rw [h]
  exact AlgEquiv.restrictNormal_commutes (FrobQ l ^ i) ↥(K0 K) x

theorem σE_pow_eq_one_iff (K : FinExt l) (i : ℕ) :
    σE K ^ i = 1 ↔ Module.finrank ℚ_[l] ↥(K0 K) ∣ i := by
  rw [← pow_fixes_iff (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) i]
  constructor
  · intro h x hx
    have := σE_pow_coe K i ⟨x, hx⟩
    rw [h] at this
    exact this.symm
  · intro h
    ext x
    rw [σE_pow_coe]
    exact h x x.2

theorem orderOf_σE (K : FinExt l) : orderOf (σE K) = Module.finrank ℚ_[l] ↥(K0 K) := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((σE_pow_eq_one_iff K _).2 dvd_rfl)
  · exact (σE_pow_eq_one_iff K _).1 (pow_orderOf_eq_one _)

def emb {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  (IntermediateField.inclusion hle).comp ((σE K ^ (-i).val : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K)) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

theorem emb_coe {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (x : ↥(K0 K)) : ((emb hle i x : ↥LL.1) : Om l) = (((σE K ^ (-i).val) x : ↥(K0 K)) : Om l) := rfl

theorem σE_pow_val_eq {K : FinExt l} {a b : ℕ}
    (h : (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) = (b : ZMod _)) : σE K ^ a = σE K ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_σE]
  exact (ZMod.natCast_eq_natCast_iff a b _).1 h

theorem emb_σ {K LL : FinExt l} (hle : K0 K ≤ LL.1) (τ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K)) (hτ : τ = σ K)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) : (emb hle (i + 1)).comp τ = emb hle i := by
  subst hτ
  have h : σE K ^ (-(i + 1)).val * σE K = σE K ^ (-i).val := by
    rw [← pow_succ]
    apply σE_pow_val_eq
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  ext x
  rw [AlgHom.comp_apply, emb_coe, emb_coe, ← h]
  rfl

end Formalism.L2.LocGap.Gal
