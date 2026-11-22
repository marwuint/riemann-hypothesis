import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChange
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A}
    (h : IsFrame bk B t p) (k : Hom B B') : IsFrame bk B' (k.f t) (k.f p) := by
  refine ⟨?_, k.f_str _ p h.2⟩
  rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ B B' k, h.1, Ideal.map_span, Set.image_singleton]

theorem env_inl_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A),
    IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  intro l _ K bk B t p hF En
  refine ⟨⟨fun m => (_root_.GlobalTheory.BSP.envFF l K bk B t p En m).flat, fun B' k => ?_⟩, _root_.GlobalTheory.BSP.envFF l K bk B t p En⟩
  obtain ⟨En'⟩ := _root_.GlobalTheory.BSP.nonempty_env l K bk B' (k.f t) (k.f p) (isFrame_map hF k)
  obtain ⟨k', hk'⟩ := _root_.GlobalTheory.BSP.env_isPO l K bk B B' t p k En En'
  exact ⟨En'.Q, k', En'.inl, hk'⟩

end GlobalTheory.BSP
