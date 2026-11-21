import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.ExhGood

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_map_injective_right {r t N : ℕ} (e : Fin r ⊕ Fin t ≃ Fin N) {U W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    {ρ : Representation ℂ (GL (Fin t) k) W} {ρ' : Representation ℂ (GL (Fin t) k) W'} (f : ρ.IntertwiningMap ρ')
    (hf : Function.Injective f) :
    ∃ F : (ind₂ e (extTensor σ ρ)).IntertwiningMap (ind₂ e (extTensor σ ρ')), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two e)
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem pair_equiv {N : ℕ} (y : Fin 2 → IrrGL k) (hd : ∑ i, (y i).1 = N) {a : IrrGL k} (ha : y 0 = a)
    (h : a.1 + (y 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor a.rep (y 1).rep)).Equiv (prodIrr y hd)) := by
  subst ha h
  exact nonempty_prod₂_equiv_prodIrr_rep y hd

theorem embed_family {N c : ℕ} (y : Fin 2 → IrrGL k) (v : Fin (c + 1) → IrrGL k) (t : Fin c → IrrGL k)
    (h0 : y 0 = v 0) (hs : ∀ i, v i.succ = t i) (hd : ∑ i, (y i).1 = N) (hv : ∑ i, (v i).1 = N)
    (ht : ∑ i, (t i).1 = (y 1).1) (g : (y 1).rep.IntertwiningMap (prodIrr t ht)) (hg : Function.Injective g) :
    ∃ F : (prodIrr y hd).IntertwiningMap (prodIrr v hv), Function.Injective F := by
  have e : t = fun i => v i.succ := funext fun i => (hs i).symm
  subst e
  have h : (v 0).1 + (y 1).1 = N := by
    rw [← h0, ← hd, Fin.sum_univ_two]
  have A0 := pair_equiv y hd h0 h
  have B0 := GlobalTheory.ProdReorder.multiProd_head (k := k) (d := fun i => (v i).1) (fun i => (v i).rep)
    (stdBlocks (fun i => (v i).1) hv) h (stdBlocks (fun i : Fin c => (v i.succ).1) ht)
  have F0 := ind₂_map_injective_right (stdSum h) (v 0).rep g hg
  obtain ⟨A⟩ := A0
  obtain ⟨B⟩ := B0
  obtain ⟨F, hF⟩ := F0
  exact ⟨(B.symm.toIntertwiningMap.comp F).comp A.symm.toIntertwiningMap,
    B.symm.toLinearEquiv.injective.comp (hF.comp A.symm.toLinearEquiv.injective)⟩

theorem isOrderedForm_snoc {h : ℕ} {Δ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔫)
    (s : Segment k) (hs : ∀ D ∈ 𝔫, ¬ D.Precedes s) :
    IsOrderedForm (Fin.snoc (α := fun _ => Segment k) Δ s) (𝔫 + {s}) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← H.1, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simpa using (Multiset.coe_add _ [s]).symm
  · induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hs _ (H.1 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
    | cast j =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc]
      exact H.2 i j (by simpa using hij)

end GlobalTheory.CompanionTheory.ExhGood

end
