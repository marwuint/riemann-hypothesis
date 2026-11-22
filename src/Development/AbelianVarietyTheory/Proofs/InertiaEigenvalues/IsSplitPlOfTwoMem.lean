import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeInertUnramified
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DefiniteFormInstances

noncomputable section

namespace GlobalTheory.BaseChangeExistsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Matrix
open GlobalTheory.IndefiniteRowSideFullHecke

section Definite

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_hD (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x : S.V) :
    τ (S.hD x x) = star (fun a => τ (S.frame.repr x a)) ⬝ᵥ
      (S.gram.map τ *ᵥ fun a => τ (S.frame.repr x a)) := by
  rw [HSpace.hD, hT_expand]
  simp only [map_sum, map_mul, hτ, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply,
    mul_assoc]
  rfl

theorem denseRange_emb [IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure τ.fieldRange) with h | h
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : τ x ∈ τ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    simp
  · have : closure (Set.range τ) = Set.univ := congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h
    exact dense_iff_closure_eq.2 this

theorem closed_of_coords [IsTotallyComplex E] (S : HSpace E) (τ : E →+* ℂ) {C : Set (Fin S.rank → ℂ)}
    (hC : IsClosed C) (h : ∀ x : S.V, (fun a => τ (S.frame.repr x a)) ∈ C) (y : Fin S.rank → ℂ) : y ∈ C := by
  have hd : DenseRange (Pi.map fun (_ : Fin S.rank) => (τ : E → ℂ)) :=
    DenseRange.piMap fun _ => denseRange_emb τ
  refine hd.induction_on y hC fun v => ?_
  have := h (S.frame.equivFun.symm v)
  have e : (fun a => τ (S.frame.repr (S.frame.equivFun.symm v) a)) =
      Pi.map (fun (_ : Fin S.rank) => (τ : E → ℂ)) v := by
    funext a
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  rwa [e] at this

theorem coords_ne_zero (S : HSpace E) (τ : E →+* ℂ) {x : S.V} (hx : x ≠ 0) :
    (fun a => τ (S.frame.repr x a)) ≠ 0 := by
  intro h
  apply hx
  rw [← S.frame.repr.map_eq_zero_iff]
  ext a
  simpa using congrFun h a

theorem continuous_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun y : Fin n → ℂ => (star y ⬝ᵥ (M *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem sig_pos_iff [IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (S.rank, 0) ↔ ∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_pos _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, 0 ≤ (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re := fun y =>
      closed_of_coords S τ (isClosed_le continuous_const (continuous_quad (S.gram.map τ))) (fun x => by
        show (0 : ℝ) ≤ _
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hq : (S.sig τ).2 = 0 := by
      by_contra hq
      have h1 := hall (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext (by simp only; omega) hq

theorem sig_neg_iff [IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (0, S.rank) ↔ ∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0 := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_neg _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re ≤ 0 := fun y =>
      closed_of_coords S τ (isClosed_le (continuous_quad (S.gram.map τ)) continuous_const) (fun x => by
        show _ ≤ (0 : ℝ)
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hp : (S.sig τ).1 = 0 := by
      by_contra hp
      have h1 := hall (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext hp (by simp only; omega)

end Definite

theorem unram_of_cm (D : D7) (hc : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _) (w : PlE D.host) :
    Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 hU ⟨w.asIdeal, w.isPrime⟩

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

end Concl

end GlobalTheory.BaseChangeExistsCompare

end
