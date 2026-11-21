import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.ThK.SplitLoc

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a a' : ℕ}

abbrev stdE (a a' : ℕ) : Fin a ⊕ Fin a' ≃ Fin (a + a') := stdSum (rfl : a + a' = a + a')

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isBlockUpper_iff (b : GL (Fin (a + a')) k) : IsBlockUpper b ↔ b ∈ parab k (two (stdE a a')) :=
  (mem_parab_two k).symm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkA (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false) : kˣ) : k) = (blkA (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkD (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true) : kˣ) : k) = (blkD (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

theorem law_parab {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β)
    (p : parab k (two (stdE a a'))) (h : GL (Fin (a + a')) k) :
    F (p * h) = indFac a a' α β (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false))
      (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true)) * F h :=
  hF.2 _ h ((isBlockUpper_iff _).2 p.2) _ _ (det_blkA p) (det_blkD p)

abbrev rhoD (a a' : ℕ) (α β : kˣ →* ℂˣ) : Representation ℂ (Levi k (Two (Fin a) (Fin a'))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin a) α) (detRep (Fin a') β)).comp (leviTwo k (Fin a) (Fin a')).symm.toMonoidHom

theorem twist_rhoD (α β : kˣ →* ℂˣ) (g : Levi k (Two (Fin a) (Fin a'))) (x : ℂ ⊗[ℂ] ℂ) :
    twist (rhoD a a' α β) (deltaHalf k (Two (Fin a) (Fin a'))) g x =
      indFac a a' α β (GeneralLinearGroup.det (g false)) (GeneralLinearGroup.det (g true)) • x := by
  obtain ⟨g, rfl⟩ := (leviTwo k (Fin a) (Fin a')).surjective g
  rw [twist_apply, deltaHalf_two]
  have h : ∀ x, rhoD a a' α β (leviTwo k (Fin a) (Fin a') g) x =
      ((α (GeneralLinearGroup.det g.1) : ℂ) * β (GeneralLinearGroup.det g.2)) • x := by
    intro x
    show extTensor _ _ ((leviTwo k (Fin a) (Fin a')).symm (leviTwo k (Fin a) (Fin a') g)) x = _
    rw [MulEquiv.symm_apply_apply]
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul v w =>
      rw [extTensor_tmul]
      simp only [detRep, ofChar_apply, detChar_apply, ← smul_eq_mul, TensorProduct.smul_tmul_smul]
  rw [h, smul_smul]
  congr 1
  simp only [Fintype.card_fin, Units.val_mul]
  show apow (GeneralLinearGroup.det g.1) ((a' : ℂ) / 2) * apow (GeneralLinearGroup.det g.2) (-(a : ℂ) / 2) * _ =
    indFac a a' α β (GeneralLinearGroup.det g.1) (GeneralLinearGroup.det g.2)
  unfold indFac
  ring

def toFn (a a' : ℕ) (α β : kˣ →* ℂˣ) : IndSp (two (stdE a a')) (rhoD a a' α β) →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ) where
  toFun f := fun g => TensorProduct.lid ℂ ℂ (f.1.1 g)
  map_add' f f' := funext fun g => map_add (TensorProduct.lid ℂ ℂ) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := funext fun g => map_smul (TensorProduct.lid ℂ ℂ) c (f.1.1 g)

theorem exists_toFn {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β) :
    ∃ f, toFn a a' α β f = F := by
  obtain ⟨U, hU, hUF⟩ := hF.1
  refine ⟨⟨⟨fun g => (TensorProduct.lid ℂ ℂ).symm (F g), fun p g => ?_⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hU.mem_nhds U.one_mem) fun u hu => ?_)⟩, funext fun g => ?_⟩
  · refine Eq.trans ?_ (twist_rhoD α β (leviProj k (two (stdE a a')) p) _).symm
    rw [← map_smul, smul_eq_mul]
    exact congrArg _ (law_parab hF p g)
  · exact Subtype.ext (funext fun x => congrArg (TensorProduct.lid ℂ ℂ).symm (hUF u hu x))
  · exact (TensorProduct.lid ℂ ℂ).apply_symm_apply _

end PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThK.SplitDict

open PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil GlobalTheory.SmGL

theorem induced_vanish_of_vanish_on_integral : IndIwasawa := by
  intro k _ _ _ _ a a' α β F hF h0
  funext g
  obtain ⟨p, hp, c, hc, rfl⟩ := iwasawa_blockTriangular k _ (fun i => (blk (two (stdE a a')) i).toNat) g
  have hp' : p ∈ parab k (two (stdE a a')) := fun i j hij => hp (by
    revert hij
    dsimp only
    cases blk (two (stdE a a')) i <;> cases blk (two (stdE a a')) j <;> simp)
  exact (law_parab hF ⟨p, hp'⟩ c).trans (by rw [h0 c hc, mul_zero]; rfl)

end PositivityTheory.ThK.SplitDict
