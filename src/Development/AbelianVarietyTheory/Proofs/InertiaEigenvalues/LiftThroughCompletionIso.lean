import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceComponentUnitaryAdelicDetermined
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSubgroupOfTrivOutsideOfLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockLiftIdentityMemUnipotentLevelCharacterOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftOther

theorem proj_eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    s.proj z = (Algebra.TensorProduct.lift s.i (AlgHom.id (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)))
      (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.SplitLift.proj_tmul, GlobalTheory.InertUmax.compAt_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem loc_eq_one_of_compAt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x : GAf L n) (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1) : s.loc n x = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  have e := congrFun (congrFun h a) b
  simp only [Matrix.map_apply] at e
  change s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) a b) = (1 : Matrix (Fin n) (Fin n) _) a b
  rw [proj_eq_comp, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLiftN_map' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcs : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (r q : ℕ) (g : GL (Fin r) (ZMod q))
    (M : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hM : IsLiftAt s r q g M) :
    IsLiftN g (Matrix.GeneralLinearGroup.map c.toRingHom M) := by
  have hv := GlobalTheory.SplitConjVal.valuation_eq s c hc hcs
  intro a b
  have h := hM a b
  split_ifs at h ⊢ with hab
  · rw [GlobalTheory.BlockConj.valued_lt_one_iff_w]
    have e : (Matrix.GeneralLinearGroup.map c.toRingHom M).val a b -
        (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : s.w.adicCompletion L) =
        c (M.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val :
          s.v.adicCompletion (maximalRealSubfield L))) := by
      rw [map_sub, map_natCast]; rfl
    rw [e, hv]; exact h
  · change c (M.val a b) = 1
    rw [h, map_one]
  · change c (M.val a b) = 0
    rw [h, map_zero]

end GlobalTheory.LiftOther

namespace GlobalTheory.LiftOther

theorem gPl_finite (D : D7) : (PendOf.gPl D).Finite := by
  classical
  choose S hS using GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D
  refine (Set.finite_range fun kv => (S kv).v).subset ?_
  rintro w ⟨kv, hkv⟩
  refine ⟨kv, HeightOneSpectrum.ext ?_⟩
  rw [← (S kv).w_under, hS kv]
  exact hkv

theorem over_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : NG.OverPl s.w w) : s.v = w :=
  HeightOneSpectrum.ext (s.w_under.symm.trans h)

theorem map_inv_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : GAf L n) : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [← Matrix.map_mul]; rfl

theorem map_inv_mul_self {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : GAf L n) : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  rw [← map_inv_mul, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LiftOther
