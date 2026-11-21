import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

end Piece

end GlobalTheory.BCGal

end
