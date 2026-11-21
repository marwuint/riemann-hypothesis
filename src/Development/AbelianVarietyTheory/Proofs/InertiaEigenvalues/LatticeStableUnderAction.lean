import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

end GlobalTheory.LatKeep
