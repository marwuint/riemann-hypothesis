import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecond
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValMulVecLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertEigSat

open Formalism.IndefR Formalism.IndefR.Links in

theorem real_cast {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {X : GlobalTheory.NJoin.RealAt D cf nch tp} {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (k : ℕ)
    (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) :
    ∃ e : (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W, ∀ (x : D.what₂.Mt μ (j.1 + 1)) h,
      (M μ k p1 p2).real (hk ▸ x) h = e (X.fn hμ j x ((A.PV j).ψ ((A.a j)⁻¹ * h))) := by
  subst hk
  exact ⟨A.eW μ hμ j, A.real μ hμ j⟩

theorem cast_eq_zero {D : D7} {μ : D.what₂.Tup} {a k : ℕ} (hk : a = k) (x : D.what₂.Mt μ a)
    (h : (hk ▸ x : D.what₂.Mt μ k) = 0) : x = 0 := by
  subst hk
  exact h

open Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Mult Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_ext {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ w ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP w) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V w d R) (z : ℂ)
    (he : hkF V w (Finsupp.single d 1) f = z • f) (g : GA D V) :
    ∑ γ ∈ R, c.ext f (g * γ) = z • c.ext f g := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
  obtain ⟨hk, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 hw
  have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR).2 _
    (GlobalTheory.PRep.rightReg ℂ (GA D V) c.W) (c.ext f) fun k hkk => funext fun g =>
      GlobalTheory.DefLiftHecke.ext_level c hc hf (hk k hkk).1 (hk k hkk).2 g
  have h3 := congrFun h2 g
  have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
  rw [he, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_smul] at h4
  rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
    Finset.sum_apply] at h3
  exact h3.trans h4.symm

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Theta GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_extV {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) (j : Fin D.R.m) (t : X.T) (h) (hh : IsOpsV X.R j t h)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hG : Good X.R t w) {d : List ℤ} {R : Finset (GA D (Vc D j))}
    (hR : SphOp (Vc D j) w d R) (y : (X.R.HV j t).H) (c : ℂ) (hy : h w (Finsupp.single d 1) y = c • y) (g) :
    ∑ γ ∈ R, X.R.extV j t y (g * γ) = c • X.R.extV j t y g :=
  have hC := X.given.core
  sum_ext (X.R.cV j) (hC.models.cV j) (hC.lev.βV j) (L := X.R.datVt j t) hG
    ((hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)) hR c
    ((hh w hG _ y).symm.trans ((congrArg (X.R.HV j t).e hy).trans (map_smul _ _ _))) g

end GlobalTheory.InertEigSat

end
