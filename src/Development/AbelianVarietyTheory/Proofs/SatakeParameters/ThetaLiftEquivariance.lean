import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta

theorem thetaKO_act {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
    (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
    (h' : Formalism.L2.Theta.GA D V) (g' : Formalism.L2.Theta.GA D W) (p : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W)
    (f : WO V W → ℂ) : thetaKO om h' g' (om p f) = thetaKO om (h' * p.1) (g' * p.2) f := by
  simp only [thetaKO]
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

theorem fin_frame_surj {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) : ∃ y, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) = k := by
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V k
  obtain ⟨y, rfl⟩ := PV.onto g hg
  exact ⟨y, rfl⟩

theorem preF_frame {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (y : Formalism.AUTREP.GAf D.host.E n) : preF PV ((Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = y := by
  classical
  have h : ∃ x, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ x) = (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) :=
    ⟨y, rfl⟩
  unfold preF
  rw [dif_pos h]
  exact PV.inj (GlobalTheory.SplitHeckeAdj.fin_inj V (PV.into _) (PV.into _) h.choose_spec)

theorem preF_mul {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) (y : Formalism.AUTREP.GAf D.host.E n) :
    preF PV (k * (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = preF PV k * y := by
  obtain ⟨z, rfl⟩ := fin_frame_surj PV k
  rw [← map_mul, ← map_mul, preF_frame, preF_frame]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem lift_actM {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (g : Formalism.AUTREP.GAf D.host.E n)
    (T : Formalism.IndefR.Mult.MMap M) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ)) (x : GA D V) :
    PiTensorProduct.lift (Formalism.IndefR.principalLevelFrame.actM PW M g T) u x = PiTensorProduct.lift T u (x * PW.ψ g) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, Formalism.IndefR.principalLevelFrame.actM_apply]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem lift_left {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel V Sp) (T : Formalism.IndefR.Mult.MMap M)
    (hT : ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ))
    (γ : GA D V) (hγ : γ ∈ GQ V) (x : GA D V) :
    PiTensorProduct.lift T u (γ * x) = PiTensorProduct.lift T u x := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, hT f γ hγ x]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

def LeftInvM {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap M) where
  carrier := {T | ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x}
  add_mem' := by
    intro T T' hT hT' v γ hγ x
    simp only [MultilinearMap.add_apply, Pi.add_apply, hT v γ hγ x, hT' v γ hγ x]
  zero_mem' := by intro v γ hγ x; rfl
  smul_mem' := by
    intro c T hT v γ hγ x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, hT v γ hγ x]

theorem minf_le_leftInv {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Formalism.IndefR.principalLevelFrame.Minf θ PW M ≤ LeftInvM M := by
  refine iSup_le fun N => Submodule.span_le.2 fun T hT v γ hγ x => ?_
  exact (hT.aut v).left γ hγ x

theorem yv_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    yv hc y x = PiTensorProduct.lift (eC hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl

end GlobalTheory.ThetaTri

end
