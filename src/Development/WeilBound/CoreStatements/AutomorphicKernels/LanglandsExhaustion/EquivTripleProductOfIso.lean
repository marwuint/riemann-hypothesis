import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import BuildAid.D4

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in
theorem product_append_iso {p q r t : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (h : ∑ a, (Fin.append x y a).1 = r + t) : Iso (two rfl (pr x hx) (pr y hy)) (pr (Fin.append x y) h) :=
  _root_.GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k p q r t x y hx hy h

theorem pr_app {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (z : Fin c → IrrGL k)
    (e : List.ofFn z = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (z a).1 = N)
    (h : r + t = N) : Iso (pr z hz) (two h (pr x hx) (pr y hy)) := by
  subst h
  have h' : ∑ a, (Fin.append x y a).1 = r + t := by
    rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  exact iso_trans (pr_congr (e.trans (List.ofFn_fin_append x y).symm) hz h') (iso_symm (product_append_iso x y hx hy h'))

theorem sum_get_eq' (L : List (IrrGL k)) : ∑ a, (L.get a).1 = (L.map fun x => x.1).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp

theorem stage3_iso (A M B : List (IrrGL k)) {N nA nM nB m' : ℕ} (hd : ∑ a, ((A ++ M ++ B).get a).1 = N)
    (hA : ∑ a, (A.get a).1 = nA) (hM : ∑ a, (M.get a).1 = nM) (hB : ∑ a, (B.get a).1 = nB)
    (h2 : nM + nB = m') (h1 : nA + m' = N) :
    Iso (pr (A ++ M ++ B).get hd) (two h1 (pr A.get hA) (two h2 (pr M.get hM) (pr B.get hB))) := by
  have hMB : ∑ a, ((M ++ B).get a).1 = m' := by
    rw [sum_get_eq', List.map_append, List.sum_append, ← sum_get_eq', ← sum_get_eq', hM, hB, h2]
  exact iso_trans (pr_app A.get (M ++ B).get _ ((List.ofFn_get _).trans ((List.append_assoc A M B).trans (congrArg₂ _ (List.ofFn_get A).symm (List.ofFn_get (M ++ B)).symm))) hA hMB hd h1)
    (two_congr h1 (iso_refl _) (pr_app M.get B.get _ (by simp only [List.ofFn_get]) hM hB hMB h2))

end PositivityTheory.Exh

end
