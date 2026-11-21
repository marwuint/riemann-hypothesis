import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperArithmeticGroupUnipotentUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletely
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponents

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn.Definite

theorem free_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E → ∀ (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → LevelHyp M → ∀ (u : U) (c : C), u • c = c → u = 1 := by
  intro E _ _ _ hbal hsmall r U C _ _ M hdef hlev u c huc
  obtain ⟨g, hsplit, hg, hunip⟩ := hlev
  obtain ⟨Γo, hst, hun, hmem⟩ := GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary E r U C M c g hunip
  obtain ⟨x, hx, hnc, -⟩ := hbal r (M.comp c)
  have h1 : M.tr u c = 1 :=
    hsmall r (M.comp c) g (_root_.GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely E g hsplit) hg Γo hst hun x hx hnc (M.tr u c) (hmem u huc)
      (fun τ => _root_.GlobalTheory.DefiniteOpNorm.opNormLe_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) x hx _
        (hst _ (hmem u huc)).1 τ)
  exact M.tr_faithful u c huc (by rw [h1]; exact (M.comp c).Γ.one_mem)

theorem share_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ _ M hdef ka ρ hρ
  classical
  haveI : Fintype C := Fintype.ofFinite C
  have hfin : Module.Finite ℂ (M.cusp ka) :=
    _root_.GlobalTheory.cusp_finite_of_comp E r U C M ka (fun c =>
      _root_.GlobalTheory.DefiniteFin.finiteDimensional_cusp_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) _)
  refine ⟨hfin, fun H hH => ?_⟩
  haveI : FiniteDimensional ℂ (M.cusp ka) := hfin
  have hfree : ∀ (h : H) (c : C), h • c = c → h = 1 :=
    free_of_definite E (GlobalTheory.T.existsBalancedFrameCMUnitary_proof E) (_root_.GlobalTheory.SmallElement.smallElement E) r H C (sub M H) hdef hH
  obtain ⟨A, hA, hAρ⟩ := _root_.GlobalTheory.ShareOn.cusp_decomp E r U C M ka ρ hρ
  have hAρH : ∀ (h : H) (x : C), ∀ v ∈ A x, ρ h v ∈ A (h • x) := fun h x v hv => hAρ h x v hv
  exact ⟨_root_.GlobalTheory.BadCount.embReg_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH,
    fun lam => _root_.GlobalTheory.BadCount.card_mul_finrank_eig_of_free ℂ U (M.cusp ka) C ρ H hfree A hA hAρH H le_rfl lam⟩

end GlobalTheory.ShareOn.Definite
