import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaFormV

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frame

variable {D : D7} {V : HSp D} {n : ℕ}

theorem fin_preF (PV : principalLevelFrame.RowPsi V n) (k : Bridge.Gf V) :
    (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  unfold preF
  rw [dif_pos hex]
  exact hex.choose_spec

theorem preF_fin (PV : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    preF PV ((finHom V).rangeRestrict (PV.ψ x)) = x := by
  apply PV.inj
  have e1 : finHom V (PV.ψ (preF PV ((finHom V).rangeRestrict (PV.ψ x)))) = finHom V (PV.ψ x) :=
    congrArg Subtype.val (fin_preF PV _)
  refine inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V
    ((GfC V).mul_mem ((GfC V).inv_mem (PV.into _)) (PV.into _)) ?_)
  show finHom V _ = 1
  rw [map_mul, map_inv, e1, inv_mul_cancel]

theorem preF_mul (PV : principalLevelFrame.RowPsi V n) (k₁ k₂ : Bridge.Gf V) :
    preF PV (k₁ * k₂) = preF PV k₁ * preF PV k₂ := by
  have h := preF_fin PV (preF PV k₁ * preF PV k₂)
  rwa [map_mul, map_mul, fin_preF, fin_preF] at h

theorem ext_apply (c : CoefA V) (f : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h)) := rfl

theorem mem_adForms_one (c : CoefA V) (f : Bridge.Gf V → c.W)
    (hf : ∀ γ ∈ GQ V, ∀ k, f ((finHom V).rangeRestrict γ * k) = c.ρ γ (f k))
    (J : Subgroup (Bridge.Gf V)) (hJ : ∀ q ∈ J, ∀ k, f (k * q) = f k) :
    f ∈ Bridge.AdForms ((finHom V).rangeRestrict.comp (GQ V).subtype) (c.ρ.comp (GQ V).subtype) J 1 := by
  intro γ h k
  have e1 := hJ k k.2 ((finHom V).rangeRestrict (γ : GA D V) * h)
  have e2 := hf γ γ.2 h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact e1.trans e2

end Frame

section Main

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

def fFin (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Bridge.Gf (Vc D j) → (X.R.cV j).W :=
  fun k => (eWloc A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))

theorem fV_eq_ext (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    fV A i j hj hμ F = (X.R.cV j).ext (fFin A i j hj hμ F) := rfl

end Main

theorem eventually_cong_preF {D : D7} {V : HSp D} {n : ℕ} (PV : principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hstd : GlobalTheory.NJoin.StdFrame hF PV) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), NG.Cong D.host.E n N (preF PV ((finHom V).rangeRestrict κ)) := by
  obtain ⟨N', hN', himg⟩ := GlobalTheory.LatCongImage.finCong_mem_levN D V n PV hF hstd N hN
  filter_upwards [GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN'] with κ hκ
  obtain ⟨κ', hκ', e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V ((finHom V).rangeRestrict κ)
  have hc : GlobalTheory.Member.FinCong V N' κ' := by
    intro z hz
    have e' : finHom V κ' = finHom V κ := e
    rw [e']
    exact hκ z hz
  obtain ⟨x, hx, hxe⟩ := himg κ' hκ' hc
  have e2 : (finHom V).rangeRestrict κ = (finHom V).rangeRestrict (PV.ψ x) := by
    rw [hxe]; exact (Subtype.ext e).symm
  rw [e2, GlobalTheory.ThetaFormV.preF_fin]
  exact hx

end GlobalTheory.ThetaFormV

end
