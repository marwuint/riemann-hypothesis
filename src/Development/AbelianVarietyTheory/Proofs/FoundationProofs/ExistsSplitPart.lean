import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTrivialAtInertPrimesStatement

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.VacuumEven

open GlobalTheory.VacuumScalar GlobalTheory.NormSum.VacMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_scalar (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    ∃ c : ℂ, W.Om g g' e0 = c •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, -⟩ := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ k0 k1 e0 he
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := lattice_facts hc he W.nz hL hL'
  obtain ⟨hline, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k1
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hF := W.maps g g' e0 heT
  refine hline _ ⟨hF.1, fun x hx => ?_⟩ _ hTh a1
  suffices hs : Wd D (tor0 D cc δ) x (W.Om g g' e0) = W.Om g g' e0 by
    rw [hW x hx] at hs; exact congrFun hs
  have hWT : Wd D (tor0 D cc δ) x (W.Om g g' e0) ∈ TT D (tor0 D cc δ) N N' := by
    obtain ⟨hd, m, hm, hfix⟩ := hF
    refine ⟨Wd_differentiable _ hd, _, Nat.mul_pos hm (Nat.pos_of_ne_zero a4), fun y hy => ?_⟩
    have h1 := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) L L') hy) m
    have h2 := hfix _ (AddSubgroup.nsmul_mem _ hy
      ((La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N')))
    rw [smul_smul] at h1 h2
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← a3 _ h1 _ hx, add_comm, a3 _ hx _ h1,
      Module.End.mul_apply, Wl_apply, Wl_apply, h2]
    rfl
  obtain ⟨y, hy, hyW⟩ := _root_.GlobalTheory.WeilEquiv.om_wd_moved D hg1 cc δ hc.1.1 N N' e0 W g⁻¹ g g'⁻¹ g' L _ L' _ hL hL'
    (by rw [inv_mul_cancel]; exact moves_one D N) (by rw [inv_mul_cancel]; exact moves_one D N') x hx _ hF
  rw [← W.mul _ _ _ _ _ heT, inv_mul_cancel, inv_mul_cancel, W.one _ heT, ← Wl_apply y, a6 y hy] at hyW
  have := congrArg (W.Om g g') hyW
  rwa [← W.mul _ _ _ _ _ hWT, mul_inv_cancel, mul_inv_cancel, W.one _ hWT] at this

end GlobalTheory.VacuumEven
