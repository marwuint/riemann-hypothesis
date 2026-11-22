import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMul
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := _root_.GlobalTheory.PsType.grp_isOpen_isCompact k n ψ hs
  have hnear := _root_.GlobalTheory.PsType.theta_one_and_near k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (_root_.GlobalTheory.PsType.triv_ev_props k).2.2.1 _
  refine ⟨⟨hone, _root_.GlobalTheory.PsType.grp_mul_closed k n ψ ho, _root_.GlobalTheory.PsType.grp_inv_mem k n ψ ho, hoc.2, hnear.1,
    _root_.GlobalTheory.PsType.theta_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
