import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.AtSingle
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.LocalMultiplicityOneIrreducibleGL

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel PositivityTheory.ThKG.Loc
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inP_det {k : Type} [Field k] [ValuativeRel k] {d d₁ : ℕ} {e : Fin d₁ ⊕ Bool ≃ Fin d} {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) :
    h.det = h (e (.inr false)) (e (.inr false)) * h (e (.inr true)) (e (.inr true)) := by
  obtain ⟨p1, -, -, p3, p4⟩ := hh
  have e1 : h.submatrix e e = fromBlocks 1 (h.submatrix e e).toBlocks₁₂ (h.submatrix e e).toBlocks₂₁ (h.submatrix e e).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (h.submatrix e e)]
    congr 1
    ext s s'
    exact p3 s s'
  rw [← det_submatrix_equiv_self e, e1, det_fromBlocks_one₁₁, ← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, p1, p4]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

structure Eqv (om : Rep σ X W) (H : Plane E d d₁) (χ : Chr F E) (r : ℝ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (τ : UA σ W₁.J → Module.End ℂ P) (Λ : Fl F v n d →ₗ[ℂ] P) : Prop where
  aug : augAt om v ≤ LinearMap.ker Λ
  act : ∀ t h₁ m, IsLevi H t h₁ m → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H, u ∈ UAt σ W (evFin F v) → m ∈ UAt σ W (evFin F v) →
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, Acts (evFin F v) (om (1, u * m)) φ φ' →
      Λ φ' = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • τ h₁ (Λ φ)

theorem one_UAt {m : ℕ} (Y : Spc F E m) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem mul_UAt {m : ℕ} {Y : Spc F E m} {g g' : UA σ Y.J} (h : g ∈ UAt σ Y (evFin F v)) (h' : g' ∈ UAt σ Y (evFin F v)) :
    g * g' ∈ UAt σ Y (evFin F v) := fun u hu => by
  rw [show mat (g * g') - 1 = (mat g - 1) * mat g' + (mat g' - 1) by rw [show mat (g * g') = mat g * mat g' from rfl]; noncomm_ring,
    smul_add, ← Matrix.smul_mul, h u hu, h' u hu]
  simp

theorem ua_ext {t : E →ₐ[F] Fv F v} {sec} (h : IsSec σ t sec) (hJ : IsUnit W.J.det) {g g' : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v))
    (hg' : g' ∈ UAt σ W (evFin F v)) (e : (mat g).map (piW t) = (mat g').map (piW t)) : g = g' := by
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have u2 : ((mat g').map (piW t))ᵀ * W.J.map t * (mat g').map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g'
    rwa [incM_map h] at this
  have un : IsUnit (((mat g).map (piW t))ᵀ * W.J.map t) :=
    ((isUnit_transpose _).2 (GeneralLinearGroup.map (piW t) g.1).isUnit).mul
      (((isUnit_iff_isUnit_det _).2 hJ).map (t : E →+* Fv F v).mapMatrix)
  refine Subtype.ext (Units.ext (h.extM (z := mat g) (z' := mat g') (fun u hu => ?_) e (un.mul_left_cancel (by rw [u1, e, u2]))))
  rw [show mat g - mat g' = (mat g - 1) - (mat g' - 1) by abel, smul_sub, hg u hu, hg' u hu, sub_zero]

theorem acts_ex {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ : ℕ} (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂)
    {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E} (hom : M.IsWeil B.ψ χX χW om) (t : E →ₐ[F] Fv F v) :
    (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ := by
  obtain ⟨⟨ι₀, hι⟩, -, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  exact ⟨sW, fun h hh φ hφ => let ⟨φ₁, h1, h2, _⟩ := (k ι₀ hι).2 h hh (GeneralLinearGroup.map (piW t) h.1) rfl φ hφ; ⟨φ₁, h1, h2⟩⟩

theorem acts_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T 0 0 := fun r _ => by
  rw [show tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 from funext fun _ => zero_mul _, map_zero]

theorem acts_lin {κ : Type} [Fintype κ] {T : Module.End ℂ ((κ → AF F) → ℂ)} (ex : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁)
    {a b a₁ b₁ : (κ → Fv F v) → ℂ} (ha : a ∈ SB _) (hb : b ∈ SB _) (h1 : Acts (evFin F v) T a a₁) (h2 : Acts (evFin F v) T b b₁) (c : ℂ) :
    Acts (evFin F v) T (a + c • b) (a₁ + c • b₁) := fun r hr => by
  by_cases h0 : a + c • b = 0
  · have key : a₁ + c • b₁ = 0 := by
      by_cases hb0 : b = 0
      · rw [hb0] at h2 h0
        rw [smul_zero, add_zero] at h0
        rw [h0] at h1
        rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), action_uniqueness F κ v T 0 (zero_mem _) _ _ h2 (acts_zero T)]
        simp
      · have ea : a = (-c) • b := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
        by_cases hc : c = 0
        · rw [hc, neg_zero, zero_smul] at ea
          rw [ea] at h1
          rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), hc]
          simp
        have : Acts (evFin F v) T a ((-c) • b₁) := fun r hr => by
          have hr' := adjoint_statement.rest F κ v r a ha (by rw [ea]; exact smul_ne_zero (neg_ne_zero.2 hc) hb0) hr b hb
          have e1 : ∀ f : (κ → Fv F v) → ℂ, tens (evFin F v) ((-c) • f) r = (-c) • tens (evFin F v) f r := fun f =>
            funext fun _ => by simp [tens, mul_assoc]
          rw [ea, e1, e1, map_smul, h2 r hr']
        rw [action_uniqueness F κ v T a ha _ _ h1 this]
        simp
    rw [h0, key]
    exact acts_zero T r (h0 ▸ hr)
  · have hs := add_mem ha ((SB _).smul_mem c hb)
    have e1 : ∀ f g : (κ → Fv F v) → ℂ, tens (evFin F v) (f + c • g) r = tens (evFin F v) f r + c • tens (evFin F v) g r := fun f g =>
      funext fun _ => by simp [tens, mul_assoc, add_mul]
    rw [e1, e1, map_add, map_smul, h1 r (adjoint_statement.rest F κ v r _ hs h0 hr a ha), h2 r (adjoint_statement.rest F κ v r _ hs h0 hr b hb)]

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
