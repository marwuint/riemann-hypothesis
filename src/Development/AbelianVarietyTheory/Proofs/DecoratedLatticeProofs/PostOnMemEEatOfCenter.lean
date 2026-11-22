import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

set_option maxHeartbeats 800000

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

namespace GlobalTheory.MiTop.CentralShift

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem actL_rTr_of_center (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank) (g0 : G0 Ld.Pg Ld.r)
    {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    actL V β Ld g0 (rTr V z f) = rTr V z (actL V β Ld g0 f) := by
  funext x
  show actG0 V β Ld g0 (rTr V z f) x = actG0 V β Ld g0 f (x * z)
  unfold actG0
  split_ifs with hk
  · simp only [rTr]
    rw [mul_assoc x hk.choose z, mul_assoc x z hk.choose, Subgroup.mem_center_iff.mp hz hk.choose]
  · rfl

theorem gaL_rTr_of_center {G : Type} [Group G] [Fintype G] (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 Ld.Pg Ld.r) (c : G → ℂ) {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    gaL V β Ld eG c (rTr V z f) = rTr V z (gaL V β Ld eG c f) := by
  unfold gaL
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, actL_rTr_of_center β Ld _ hz]
  simp [rTr, Finset.sum_apply]

theorem ipM_eq_of_iff (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {T T' U U' : MMap M}
    (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) : ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem map_mul_right_center (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) {z : GA D V}
    (hz : z ∈ Subgroup.center (GA D V)) : Measure.map (fun g => g * z) μ = μ := by
  have e : (fun g : GA D V => g * z) = fun g => z * g := funext fun g => Subgroup.mem_center_iff.mp hz g
  rw [e]
  exact map_mul_left_eq_self μ z

theorem lift_postOn (T : MMap M) (z : GA D V) (v : SmT M) :
    PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) v = rTr V z (PiTensorProduct.lift T v) := by
  have : PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) =
      GlobalTheory.FinTranslate.rTrL V z ∘ₗ PiTensorProduct.lift T := by
    apply PiTensorProduct.ext
    ext w
    simp [postOn, PiTensorProduct.lift.tprod]
  rw [this]
  rfl

end General

end GlobalTheory.MiTop.CentralShift

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop

end
