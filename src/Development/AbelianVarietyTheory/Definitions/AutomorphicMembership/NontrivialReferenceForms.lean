import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeWindow
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZp
import Formalism.LocalToGlobal.Columns.RowFormsNZw

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hX : B.fields.Ok)

def md (m e j : ℕ) : ℕ := if j = m then e else 0

theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

theorem md_zero (R : Ranks) (e : ℕ) : md R.m e 0 = 0 := if_neg (by have := R.two_le_m; omega)

def what₂ : RowsRest B C :=
  { model hf 0 0 0 with
    muTw := fun w => if B.places.resChar w = B.host.pde then C.muStar' else C.muStar
    muTw_conj := fun w => by rw [GlobalTheory.Mem.Top.TwFin.resChar_conj]
    muAt_or := fun _ => Or.inl rfl
    Dall := 0
    delp := 0
    delp_le_one := zero_le_one
    D_eq := by simp [model]
    FT := Empty
    instFT := inferInstance
    instFTd := inferInstance
    ft := Fin.elim0
    ft0 := Fin.elim0
    Amb := fun μ => Eu (d μ)
    instAmb := fun _ => inferInstance
    instAmbi := fun _ => inferInstance
    instAmbf := fun _ => inferInstance
    Mult := fun μ j => Eu (md B.R.m (d μ) j)
    instMult := fun _ _ => inferInstance
    instMulti := fun _ _ => inferInstance
    instMultf := fun _ _ => inferInstance
    multZero := fun μ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (md_zero B.R (d μ)))
    multTop := fun μ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (if_pos rfl))
    io := fun _ _ => 0
    Mtilde := L
    eOp := fun _ => LinearMap.id
    eOp_idem := fun _ => rfl
    eOp_sa := fun _ _ _ => rfl
    perCol := fun u μ φ F => by
      classical
      exact if hμ : μ = C.mu0 then (C.mem u).P.PtilCol (Subtype.val φ) ((e0 u).symm (hμ ▸ F))
        else (C.PTw u μ).PtilCol (C.e0Tw u μ (Subtype.val φ)) ((eT u μ).symm F)
    Bu := fun _ _ _ => 0
    kaBig := kb
    kaSmall := ks
    isot := fun _ _ => ⊤
    lamP := fun _ _ _ => 1
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host
    eMt0 := e0
    perCol_base_eq_PtilCol := fun u φ F => by
      rw [dif_pos rfl]; rfl
    Bu_linL := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    Bu_linR := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    eMtTw := eT
    perCol_tie := fun u μ hμ φ F => by
      rw [dif_neg hμ]; rfl }

end Build

end GlobalTheory.Mem.Df.Model

end
