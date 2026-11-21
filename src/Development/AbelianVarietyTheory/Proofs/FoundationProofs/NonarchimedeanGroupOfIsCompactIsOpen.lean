import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem eq_one_of_forall_norm_pow_sub_one_le {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

theorem nonarchimedeanGroup_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

section Groups

variable {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem totallyDisconnectedSpace_GLoc (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (GLoc σ J v) := by
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  haveI : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → Fv F v ⊗[F] E))
  exact ⟨isTotallyDisconnected_of_image (f := fun g => (matHom _ σ J g).1)
    (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).continuousOn
    (Units.val_injective.comp (matHom_injective _ σ J)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem totallyDisconnectedSpace_GFin : TotallyDisconnectedSpace (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GLoc σ J
  ⟨isTotallyDisconnected_of_image (f := fun g v => projFinLoc σ J v g)
    (continuous_pi fun v => continuous_projFinLoc σ J v).continuousOn
    (fun _ _ e => GFin_ext σ J (congrFun e)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nonarchimedeanGroup_GLoc (v : HeightOneSpectrum (𝓞 F)) : NonarchimedeanGroup (GLoc σ J v) :=
  haveI := totallyDisconnectedSpace_GLoc σ J v
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_stabLoc σ J (stdLattice E m) v)
    (isOpen_stabLoc σ J (stdLattice E m) v)

theorem nonarchimedeanGroup_GFin : NonarchimedeanGroup (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GFin σ J
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_levelOffFin σ J (stdLattice E m) ∅)
    (isOpen_levelOffFin_empty σ J (stdLattice E m))

variable {σ J}

end Groups

variable {σ} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L]

end GlobalTheory.Doubling

end
