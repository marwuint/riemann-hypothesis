import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (_root_.GlobalTheory.FN.mob_props).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := _root_.GlobalTheory.FNRoots.main Ω ε
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine _root_.GlobalTheory.FN.isExp_comp_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (_root_.GlobalTheory.FN.cmp_props).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
