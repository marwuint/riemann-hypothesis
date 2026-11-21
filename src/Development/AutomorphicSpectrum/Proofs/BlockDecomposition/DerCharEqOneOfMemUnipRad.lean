import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirJac

section Abstract

variable {M V X Y : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem ker_comp_mkQ (K₁ K : Submodule ℂ V) (q : (V ⧸ K₁) →ₗ[ℂ] X) (e : LinearMap.ker q = K.map K₁.mkQ)
    (hle : K₁ ≤ K) : LinearMap.ker (q ∘ₗ K₁.mkQ) = K := by
  rw [LinearMap.ker_comp, e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

end Abstract

section Iter

variable (k : Type) [Field k]

noncomputable def embedding₂ (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (embedding₂ n j)

end Iter

section IterRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iterPhi_quotient (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ g v, q (τ.ρ (embedding₂ k n j g) v) = psiMinus k (iterPhi k ψ j τ).ρ g (q v)
  | 0, τ => ⟨Submodule.mkQ _, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ), fun _ _ => rfl⟩
  | j + 1, τ => by
    obtain ⟨q', hs, hk, hi⟩ := iterPhi_quotient ψ n j (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    obtain ⟨e, hle⟩ := GlobalTheory.CompanionTheory.BZMirStep.twKer_twAct_eq_map τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j)) _
      (levi_stab ψ (n + j)) (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) (derUnipM k (n + j + 1) n)
      (derCharM k ψ (n + j + 1) n) (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
      (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
    refine ⟨q' ∘ₗ Submodule.mkQ _, hs.comp (Submodule.mkQ_surjective _), ?_, fun g v => ?_⟩
    · exact ker_comp_mkQ _ _ q' (hk.trans e) hle
    · exact hi g (Submodule.Quotient.mk v)

end IterRep

section Concrete

variable {k : Type} [Field k]

theorem emb_inl_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (g.1 : Matrix (Fin n) (Fin n) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inl_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin n) (j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin t) (j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (g.2 : Matrix (Fin t) (Fin t) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem one_inr_inr {n t N : ℕ} (h : n + t = N) (i j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (1 : Matrix (Fin t) (Fin t) k) i j := by
  simp [one_apply]

theorem one_inl_inr {n t N : ℕ} (h : n + t = N) (i : Fin n) (j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  simp [one_apply]

theorem one_inr_inl {n t N : ℕ} (h : n + t = N) (i : Fin t) (j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  simp [one_apply]

end Concrete

section Entries

variable {k : Type} [Field k]

theorem glEmbMat_block_apply {n m : ℕ} (hnm : n ≤ m) (g : Matrix (Fin n) (Fin n) k) (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r s : Fin m, A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin m) (Fin m) k) r s) (r s : Fin (m + 1)) :
    glEmbMat k m A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r s := by
  induction r using Fin.lastCases with
  | last =>
    rw [dif_neg (fun h => by have := h.1; simp at this; omega)]
    induction s using Fin.lastCases with
    | last => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_last, one_apply_eq]
    | cast s => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_castSucc, one_apply_ne (Fin.castSucc_ne_last s).symm]
  | cast r =>
    induction s using Fin.lastCases with
    | last =>
      rw [dif_neg (fun h => by have := h.2; simp at this; omega), GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_last,
        one_apply_ne (Fin.castSucc_ne_last r)]
    | cast s =>
      rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_castSucc, hA r s]
      by_cases h : (r : ℕ) < n ∧ (s : ℕ) < n
      · rw [dif_pos h, dif_pos (by simpa using h)]
        rfl
      · rw [dif_neg h, dif_neg (by simpa using h)]
        simp [one_apply]

theorem iotaM_apply (n : ℕ) (g : GL (Fin n) k) : ∀ (j : ℕ) (r s : Fin (n + j + 1)),
    (((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s =
      if h : (r : ℕ) < n ∧ (s : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s
  | 0, r, s => glEmbMat_block_apply le_rfl (g : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k)
      (fun r s => by rw [dif_pos ⟨r.2, s.2⟩]) r s
  | j + 1, r, s => glEmbMat_block_apply (by omega) (g : Matrix (Fin n) (Fin n) k) _ (iotaM_apply n g j) r s

theorem iotaM_eq_emb (n j : ℕ) (g : GL (Fin n) k) :
    ((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1) := by
  apply Units.ext
  ext r s
  rw [iotaM_apply]
  obtain ⟨x, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective r
  obtain ⟨y, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective s
  rcases x with x | x <;> rcases y with y | y
  · rw [emb_inl_inl, dif_pos (by simp)]
    congr 1
  · rw [emb_inl_inr, dif_neg (by simp), one_inl_inr]
  · rw [emb_inr_inl, dif_neg (by simp), one_inr_inl]
  · rw [emb_inr_inr, dif_neg (by simp), one_inr_inr]
    rfl

end Entries

end GlobalTheory.CompanionTheory.BZMirJac

end
