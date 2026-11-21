import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.FinPlaceSmall

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V' hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om' (1, h)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobalPair.opFin om' v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobalPair.FinPlaceSmall

