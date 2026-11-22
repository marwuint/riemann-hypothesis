import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpansionConverges
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldAnSlGerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangularStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := _root_.GlobalTheory.FN.frac_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := _root_.GlobalTheory.FN.j_in_frac Ω ε T
  have hgerm := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  have hj := _root_.GlobalTheory.FN.jT_level_one
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (_root_.GlobalTheory.FN.inR_mdifferentiable ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (_root_.GlobalTheory.FN.frac_sl_right_action Ω ε T).1, sl_mul := (_root_.GlobalTheory.FN.frac_sl_right_action Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).1, an_sl := _root_.GlobalTheory.FN.an_sl_germ Ω ε T, an_mero := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).2,
            an_exp := fun f => (_root_.GlobalTheory.FN.frac_exp_converges Ω ε T f).2,
            level := _root_.GlobalTheory.FN.frac_exists_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := _root_.GlobalTheory.FNRecip.main Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := _root_.GlobalTheory.FN.frac_isAlgebraic_adjoin_j Ω ε T a ha, bdd := _root_.GlobalTheory.FN.frac_bdd_den Ω ε T, sat := _root_.GlobalTheory.fn_sat Ω ε T,
            mem_q := _root_.GlobalTheory.FN.exists_of_qexp Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
