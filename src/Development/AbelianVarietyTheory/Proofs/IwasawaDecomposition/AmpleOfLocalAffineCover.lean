import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

end GlobalTheory.AmpleOverBase
