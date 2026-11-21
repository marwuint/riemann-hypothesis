import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]

theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

end General

section Integrality

theorem IntAt.add {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a + b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have := ((isIntegral_natCast (R := ℤ) m).mul ha).add ((isIntegral_natCast (R := ℤ) n).mul hb)
  have e : ((n * m : ℕ) : ℂ) * (a + b) = m * (n * a) + n * (m * b) := by push_cast; ring
  rw [e]; exact this

theorem IntAt.mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

end Integrality

section Symmetry

variable {E : Type} [Field E] [NumberField E]

theorem levelLe_inv {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} : LevelLe χ⁻¹ P n ↔ LevelLe χ P n := by
  refine forall_congr' fun y => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  change (χ.loc P y)⁻¹ = 1 ↔ _
  exact inv_eq_one

theorem IsValChar.inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) :
    IsValChar (fun i => ComplexEmbedding.conjugate (φ i)) s κ 𝔣 Q χ⁻¹ := by
  obtain ⟨h1, ⟨h2, h2'⟩, h3, h4⟩ := h
  refine ⟨fun x => ?_, ⟨fun v k => ?_, fun w k => ?_⟩, (hasInfRatio_iff _ _ _).2 fun k => ?_, fun v P hP => ⟨fun hv => ?_, fun hv m => ?_⟩⟩
  · change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, h1 x, inv_one]
  · have h := h2 v k
    unfold Formalism.L2.Host.HChar.resFin at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · have h := h2' w k
    unfold Formalism.L2.Host.HChar.resInf at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · change (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val, (hasInfRatio_iff _ _ _).1 h3 k, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← inv_zpow, inv_div]
    simp
  · exact levelLe_inv.2 ((h4 v P hP).1 hv)
  · rw [levelLe_inv]; exact (h4 v P hP).2 hv m

end Symmetry

section Cyclotomic

abbrev K : Type := CyclotomicField 21 ℚ

instance : IsCyclotomicExtension {21} ℚ K := CyclotomicField.isCyclotomicExtension 21 ℚ

instance : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {21}) ⟨21, rfl, by norm_num⟩

end Cyclotomic

end GlobalTheory.CMVal.Model
