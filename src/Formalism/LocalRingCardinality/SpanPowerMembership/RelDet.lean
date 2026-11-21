import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.RelDetCore
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

section RelDet

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem smulLat_one {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

theorem smulLat_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (A * B) L = SDLat.smulLat A (SDLat.smulLat B L) := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp, Matrix.toLin'_mul]
  rfl

def orbRel (N : ℕ) : Setoid (SDLat E N) where
  r L L' := ∃ γ : Matrix.unitaryGroup (Fin N) E, L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1
  iseqv := by
    refine ⟨fun L => ⟨1, ?_⟩, fun {L L'} ⟨γ, h⟩ => ⟨γ⁻¹, ?_⟩, fun {L L' L''} ⟨γ, h⟩ ⟨γ', h'⟩ => ⟨γ' * γ, ?_⟩⟩
    · exact (smulLat_one L.1).symm
    · rw [h, ← smulLat_mul]
      have : ((γ⁻¹ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) *
          (γ : Matrix (Fin N) (Fin N) E) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
      rw [this, smulLat_one]
    · rw [h', h, ← smulLat_mul]; rfl

def orbRep {N : ℕ} (L : SDLat E N) : SDLat E N := (Quotient.mk (orbRel N) L).out

theorem orbRep_rel {N : ℕ} (L : SDLat E N) : (orbRel N) (orbRep L) L := Quotient.mk_out (s := orbRel N) L

theorem orbRep_eq {N : ℕ} {L L' : SDLat E N} (h : (orbRel N) L L') : orbRep L = orbRep L' := by
  unfold orbRep
  rw [Quotient.sound h]

def orbGam {N : ℕ} (L : SDLat E N) : Matrix.unitaryGroup (Fin N) E := Classical.choose (orbRep_rel L)

theorem orbGam_spec {N : ℕ} (L : SDLat E N) :
    L.1 = SDLat.smulLat ((orbGam L : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) (orbRep L).1 :=
  Classical.choose_spec (orbRep_rel L)

def detU {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) E) : unitary E :=
  ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩

theorem detU_mul {N : ℕ} (γ δ : Matrix.unitaryGroup (Fin N) E) : detU (γ * δ) = detU γ * detU δ := by
  apply Subtype.ext
  show ((γ * δ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E).det = _
  rw [Submonoid.coe_mul, Matrix.det_mul]
  rfl

variable {Tau : Type} [Fintype Tau] (emb : Tau → (E →+* ℂ))

def inverseEmbeddingProduct : unitary E →* ℂˣ :=
  (∏ τ : Tau, (Units.map (emb τ).toMonoidHom).comp Unitary.toUnits)⁻¹

theorem inverseEmbeddingProduct_apply (z : unitary E) : ((inverseEmbeddingProduct emb z : ℂˣ) : ℂ) = ∏ τ : Tau, (emb τ (z : E))⁻¹ := by
  simp [inverseEmbeddingProduct]

def potGen {N : ℕ} (L : SDLat E N) : ℂˣ := inverseEmbeddingProduct emb (detU (orbGam L))

def relDetGen (N : ℕ) (L L' : SDLat E N) : ℂˣ := (potGen emb L)⁻¹ * potGen emb L'

theorem relDetGen_self (N : ℕ) (L : SDLat E N) : relDetGen emb N L L = 1 := by
  simp [relDetGen]

theorem relDetGen_mul (N : ℕ) (L L' L'' : SDLat E N) :
    relDetGen emb N L L' * relDetGen emb N L' L'' = relDetGen emb N L L'' := by
  simp only [relDetGen]
  group

theorem inverseEmbeddingProduct_stabilizer_det (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    {N : ℕ} (δ : Matrix.unitaryGroup (Fin N) E) (L : SDLat E N)
    (hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 = L.1) : inverseEmbeddingProduct emb (detU δ) = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one, Finset.prod_inv_distrib, inv_eq_one]
  apply hmu
  refine det_root_of_unity_of_stab hstar (δ : Matrix (Fin N) (Fin N) E) (Matrix.det_of_mem_unitary δ.2)
    L.1 L.2.1 L.2.2.1 ?_
  intro x hx
  have : (δ : Matrix (Fin N) (Fin N) E).mulVec x ∈ SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 :=
    ⟨x, hx, by simp [Matrix.toLin'_apply]⟩
  rwa [hδ] at this

theorem relDetGen_smul (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    (N : ℕ) (L L' : SDLat E N) (γ : Matrix.unitaryGroup (Fin N) E)
    (h : L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1) :
    relDetGen emb N L L' = inverseEmbeddingProduct emb ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  have hrel : (orbRel N) L L' := ⟨γ, h⟩
  have hrep : orbRep L' = orbRep L := (orbRep_eq hrel).symm
  set r := orbRep L with hr
  set gL := orbGam L
  set gL' := orbGam L'
  have hL : L.1 = SDLat.smulLat (gL : Matrix (Fin N) (Fin N) E) r.1 := orbGam_spec L
  have hL' : L'.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
    have := orbGam_spec L'; rwa [hrep] at this
  set δ : Matrix.unitaryGroup (Fin N) E := (γ * gL)⁻¹ * gL'
  have hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) r.1 = r.1 := by
    have e1 : SDLat.smulLat ((γ * gL : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 =
        SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
      rw [Submonoid.coe_mul, smulLat_mul, ← hL, ← h, hL']
    show SDLat.smulLat (((γ * gL)⁻¹ * gL' : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = r.1
    rw [Submonoid.coe_mul, smulLat_mul, ← e1, ← smulLat_mul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact smulLat_one r.1
  have hs := inverseEmbeddingProduct_stabilizer_det emb hstar hmu δ r hδ
  have hg : gL' = (γ * gL) * δ := by
    show gL' = (γ * gL) * ((γ * gL)⁻¹ * gL')
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have : potGen emb L' = inverseEmbeddingProduct emb (detU γ) * potGen emb L := by
    simp only [potGen]
    rw [show orbGam L' = gL' from rfl, hg, detU_mul, detU_mul, map_mul, map_mul, hs, mul_one, mul_comm]
  simp only [relDetGen, this]
  rw [mul_comm (inverseEmbeddingProduct emb (detU γ)), ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

end RelDet

section Host

variable {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi))

def embTau : Tau → (H.E →+* ℂ) := fun τ => H.emb ((eTau τ : R.Psi) : R.GG)

theorem prod_embTau_eq_one_of_torsion : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, embTau H eTau τ x = 1 :=
  fun _ hx => UpperTheory.Mu.prod_emb H eTau hx

def exampleInverseEmbeddingProduct : letI := H.cmStar; unitary H.E →* ℂˣ := letI := H.cmStar; inverseEmbeddingProduct (embTau H eTau)

theorem exampleCharacter_unitary_product : letI := H.cmStar; ∀ z : unitary H.E,
    (((MonoidHom.id ℂˣ) (exampleInverseEmbeddingProduct H eTau z) : ℂˣ) : ℂ) =
      ∏ τ : Tau, (H.emb ((eTau τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  let _ := H.cmStar
  intro z
  exact inverseEmbeddingProduct_apply (embTau H eTau) z

def relDetExample : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ :=
  letI := H.cmStar; relDetGen (embTau H eTau)

theorem relDetExample_self : letI := H.cmStar; ∀ N L, relDetExample H eTau N L L = 1 := by
  let _ := H.cmStar
  exact relDetGen_self (embTau H eTau)

theorem relDetExample_mul : letI := H.cmStar; ∀ N L L' L'',
    relDetExample H eTau N L L' * relDetExample H eTau N L' L'' = relDetExample H eTau N L L'' := by
  let _ := H.cmStar
  exact relDetGen_mul (embTau H eTau)

theorem relDetExample_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      relDetExample H eTau N L L' = exampleInverseEmbeddingProduct H eTau
        ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  let _ := H.cmStar
  exact relDetGen_smul (embTau H eTau) (emb_star H) (prod_embTau_eq_one_of_torsion H eTau)

end Host

end Formalism.BasicNotions.Examples₂
