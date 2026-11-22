import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ind₂_equiv_pair (y z : IrrGL k) {N : ℕ} (h : y.1 + z.1 = N) (hd : ∑ a, (![y, z] a).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd)) := by
  subst h
  exact nonempty_prod₂_equiv_prodIrr_pair y z hd

private theorem emb_unit (x : IrrGL k) : ∃ y : IrrGL k, y.1 = 0 ∧ Emb x y x := by
  let o : IrrRep (GL (Fin 0) k) := IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one
  let y : IrrGL k := IrrGL.of o.ρ o.smooth o.irr
  have φ : o.ρ.Equiv y.rep := IrrGL.equivOf o.ρ o.smooth o.irr
  have κ : y.2.rep.V ≃ₗ[ℂ] ℂ := φ.toLinearEquiv.symm
  have h : 0 + x.1 = x.1 := Nat.zero_add _
  have hd : ∑ a, (![y, x] a).1 = x.1 := (Fin.sum_univ_two _).trans h
  obtain ⟨a⟩ := GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth
  obtain ⟨b⟩ := ind₂_equiv_pair y x h hd
  exact ⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩

end

