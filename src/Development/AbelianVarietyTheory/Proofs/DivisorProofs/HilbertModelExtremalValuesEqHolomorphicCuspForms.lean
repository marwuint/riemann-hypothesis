import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorEvalMultiplicitySpaceOntoHolomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem range_evAt_eq_adel_image : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, Set.range (evAt R i σ (v₀ i σ)) = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ))) '' (Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) : Set _) := by
  intro hc hf D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp i σ hσ hV
  obtain ⟨hs, -, w, hw⟩ := _root_.GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ hT i σ hσ
  have hg := _root_.GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV w hw
  have hχ := (_root_.GlobalTheory.HolDict.PrincLev.principal_level D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV).2.1
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 hc hf D R.θ _ _ (R.MW i σ) w _ _ _ _ _ _ _ _ _ hs hg hw (v₀ i σ)
    (hT.hv₀ i σ).1 _ hχ
  have hW := hM.HW i σ
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := hW.2.1
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    have hm : (R.HW i σ).e h ∈ R.Wall i σ := hr ▸ LinearMap.mem_range_self _ h
    obtain ⟨P, hP, e⟩ := h2 _ hm
    exact ⟨P, hP, e⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨S, hS, e⟩ := h1 P hP
    have hm : S ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hS
    obtain ⟨h, rfl⟩ := hm
    exact ⟨h, e⟩

end GlobalTheory.HolDict
