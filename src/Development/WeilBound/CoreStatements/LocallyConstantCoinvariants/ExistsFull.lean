import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W} {v : Pl F}
  {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ}

theorem augAt_le : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, φ, h, φ₁, h₁, -, rfl⟩
  exact sub_mem h₁ h)

theorem aug_le_map (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) : aug n d ν α ≤ (augAt om v).map ι := Submodule.span_le.2 (by
  rintro _ ⟨g₀, Φ, hΦ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := hb.2.2 hΦ
  obtain ⟨g, hg, h⟩ := hD.leftOnto g₀
  obtain ⟨φ₁, h₁, ha, e⟩ := h φ hφ
  exact ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, h₁, ha, rfl⟩, by rw [map_sub, e]⟩)

theorem mem_augAt (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (h : ι φ ∈ aug n d ν α) : φ ∈ augAt om v := by
  obtain ⟨ψ, hψ, e⟩ := aug_le_map hb hD h
  rwa [← hb.2.1 (augAt_le hψ) hφ e]

theorem exists_full (hS : SurjSt) (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (h1 : ν ≠ 1) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), Full (ι φ₀) ∧ φ - φ₀ ∈ augAt om v := by
  obtain ⟨Φ₀, h0, h⟩ := hS _ n d ν α hν h1 _ (hb.1 hφ)
  obtain ⟨φ₀, hφ₀, rfl⟩ := hb.2.2 h0.1
  exact ⟨φ₀, hφ₀, h0, mem_augAt hb hD (sub_mem hφ hφ₀) (by rwa [map_sub])⟩

theorem acts_zero (γ : UA σ X.J × UA σ W.J) : Acts (evFin F v) (om γ) (0 : (Fin n × Fin d → Fv F v) → ℂ) 0 := fun r _ => by
  have : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [this, map_zero]

theorem chrW_div_ne {χ χ' : Chr F E} {t : E →ₐ[F] Fv F v} (h : chrW (χ / χ') t ≠ 1) : chrW (χ' / χ) t ≠ 1 := fun e =>
  h (MonoidHom.ext fun x => by
    have := DFunLike.congr_fun e x
    simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.one_apply] at this ⊢
    rw [map_div, div_eq_one] at this ⊢
    exact this.symm)

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

def GoodSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v)

end PositivityTheory.KCo
