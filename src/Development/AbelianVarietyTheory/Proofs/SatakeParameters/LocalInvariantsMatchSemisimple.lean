import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

end Glob

end GlobalTheory.TwistLG
