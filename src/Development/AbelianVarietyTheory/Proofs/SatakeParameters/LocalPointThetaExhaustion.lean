import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PtLocalPin

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_finset {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i), f ≠ 0 →
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) →
      ∃ S' ∈ t, ∃ g ∈ S', g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert a t ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add, hyfix κ hκ hκt] at e
        exact add_left_cancel e
      by_cases hy0 : y = 0
      · subst hy0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF z hz hf0 hzfix
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨a, Finset.mem_insert_self a t, y, hy, hy0, hyfix⟩
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF f ((sup_le hle le_rfl) hf) hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem fixed_of_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g' : GAf L n → W)
    (hg' : g' ∈ S') (hg0 : g' ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g' = g') :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨T, hT⟩ := hiso
  set g : S := T.symm ⟨g', hg'⟩ with hgdef
  have hTg : T g = ⟨g', hg'⟩ := T.apply_symm_apply _
  refine ⟨g, g.2, fun h => hg0 ?_, fun κ hκ ht => ?_⟩
  · have h0 : g = 0 := Subtype.ext h
    rw [h0, map_zero] at hTg
    exact (congrArg Subtype.val hTg).symm
  · have e := hT κ g ⟨_, hS.stable κ _ g.2⟩ rfl
    rw [hTg] at e
    have e' : T ⟨NG.rt L n κ g, hS.stable κ _ g.2⟩ = T g := by
      rw [hTg]
      exact Subtype.ext (e.trans (hfix κ hκ ht))
    exact congrArg Subtype.val (T.injective e')

theorem exists_fixed_of_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (hS : NG.IsIrrRep ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) (hf0 : f ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g', hg', hg0, hgf⟩ := exists_fixed_of_finset v t ht f hft hf0 hfix
  exact fixed_of_iso hS.1 (ht hS').2 v g' hg' hg0 hgf

end Gen

theorem coeff_eq {N n : ℕ} (hN : N ≠ 0) {c c' : ℕ → ℂ}
    (h : (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c k) * X ^ (n - k) : ℂ[X]) =
      X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c' k) * X ^ (n - k))
    {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : c k = c' k := by
  have key : ∀ d : ℕ → ℂ, (X ^ n + ∑ j ∈ Finset.Icc 1 n,
      C ((-1 : ℂ) ^ j * ((N : ℂ)) ^ (j * (j - 1) / 2) * d j) * X ^ (n - j) : ℂ[X]).coeff (n - k) =
        (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * d k := by
    intro d
    rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finset_sum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj hjk
      rw [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hk
      exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) hk
  have e := congrArg (fun p : ℂ[X] => p.coeff (n - k)) h
  rw [key c, key c'] at e
  have hne : (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))
  exact mul_left_cancel₀ hne e

end GlobalTheory.PtLocalPin

end
