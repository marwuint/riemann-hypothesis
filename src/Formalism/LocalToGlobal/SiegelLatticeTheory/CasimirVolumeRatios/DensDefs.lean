import Formalism.PeriodIntegrals.LatCountG
import Formalism.HarderNarasimhan.StatementPl
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnDensNonneg
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndHsLeDist
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

namespace Formalism.L2.S.S7.DensDefs

open MeasureTheory NumberField Module
open scoped ENNReal TensorProduct
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates

variable (I : AutInst)

def inclV (u : Fin I.n → I.E) : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)

open Classical in

def ratM (x : I.GA) : GL (Fin I.n) I.E :=
  if h : x ∈ I.GFset then h.choose else 1

theorem ratM_spec {x : I.GA} (h : x ∈ I.GFset) :
    ratM I x ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      I.fmat x.2 = (ratM I x : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  unfold ratM
  rw [dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2.2⟩

theorem af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : (0 : Af F) v = (1 : Af F) v := by rw [h]
  exact zero_ne_one (α := v.adicCompletion F) h'

theorem ratM_eq {x : I.GA} (h : x ∈ I.GFset) (g : GL (Fin I.n) I.E)
    (hg : I.fmat x.2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) : ratM I x = g := by
  have h1 := (ratM_spec I h).2
  have := af_nontrivial I.F
  rw [hg] at h1
  apply Units.ext
  ext i j
  exact Formalism.UG.P.inclE_injective I.F I.E (Af I.F) (congrFun (congrFun h1 i) j).symm

theorem ratM_mul {x y : I.GA} (hx : x ∈ I.GFset) (hy : y ∈ I.GFset) : ratM I (x * y) = ratM I x * ratM I y := by
  refine ratM_eq I (rrg_mul_mem I hx hy) _ ?_
  have e : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
  rw [e, (ratM_spec I hx).2, (ratM_spec I hy).2, Units.val_mul, Matrix.map_mul]

theorem ratM_one : ratM I 1 = 1 := by
  refine ratM_eq I (one_mem_rational_points I) _ ?_
  simp [AutInst.fmat]

def PPF {a : ℕ} (W : Fin a → Submodule I.E (Fin I.n → I.E)) : Subgroup I.GA where
  carrier := {x | x ∈ I.GFset ∧ ∀ i, (W i).map (Matrix.toLin' (ratM I x : Matrix (Fin I.n) (Fin I.n) I.E)) = W i}
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    refine ⟨rrg_mul_mem I hx hy, fun i => ?_⟩
    rw [ratM_mul I hx hy, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp, hyW i, hxW i]
  one_mem' := ⟨one_mem_rational_points I, fun i => by simp [ratM_one]⟩
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    have hxi : x⁻¹ ∈ I.GFset := rrg_inv_mem I hx
    have e : ratM I x⁻¹ = (ratM I x)⁻¹ := by
      have h1 := ratM_mul I hxi hx
      rw [inv_mul_cancel, ratM_one] at h1
      exact eq_inv_of_mul_eq_one_left h1.symm
    refine ⟨hxi, fun i => ?_⟩
    conv_lhs => rw [← hxW i]
    rw [e, ← Submodule.map_comp, ← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one, Submodule.map_id]

end Formalism.L2.S.S7.DensDefs

end
