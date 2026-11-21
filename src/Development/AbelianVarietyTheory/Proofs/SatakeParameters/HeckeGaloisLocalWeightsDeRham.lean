import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjDoubleBlockOfIsoSubspacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AbsIrrConstituents

theorem mapRep_comp {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep (g.comp f) ρ = mapRep g (mapRep f ρ) := by
  ext x i j
  rfl

theorem fixedJumps_nodup (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* Qbar (D.nd.l i)) :
    (D.naut.locAutHodgeTateWeightsLevelZero i τ).Nodup := by
  have h1 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
  rw [D.nbc.embAV_inf i P] at h1
  have h2 := (D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1
  have h3 := h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)
  rw [← h1] at h3
  exact h3.of_map _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem mem_of_induces' (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  apply (h _).mp
  have e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp only [map_natCast]
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem sumRep_coe {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix _ _ k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem coe_mapRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (ρ g : Matrix (Fin a) (Fin a) k).map f := rfl

theorem mapRep_sumRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a b : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) :
    mapRep f (SumRepresentations.At.sumRep ρ ρ') = SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext g i j
  rw [coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem contQ_sumRep (D : D7) (i : D.nd.Loc) {a b : ℕ}
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (h : SumRepresentations.At.ContQ D.nd i ρ) (h' : SumRepresentations.At.ContQ D.nd i ρ') : SumRepresentations.At.ContQ D.nd i (SumRepresentations.At.sumRep ρ ρ') := by
  unfold SumRepresentations.At.ContQ at *
  simp only [sumRep_coe, Matrix.reindex_apply]
  exact (Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem rel_map' {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {a d u : ℕ} (h : d + d + u = a)
    (ρ : Γ →* GL (Fin a) k) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix _ _ k)) :
    ∀ g, (((Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm)⁻¹ *
        mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm :
          GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.reindex (finCongr h) (finCongr h)
        ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep (mapRep f σ) (mapRep f σ)) (mapRep f υ) g : GL (Fin (d + d + u)) L) :
          Matrix _ _ L) := by
  subst h
  intro g
  have e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ *
      mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm =
      Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* Matrix _ _ L).toMonoidHom
        (Pm⁻¹ * ρ g * Pm) := by
    simp only [map_mul, map_inv]; rfl
  rw [e1]
  show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _
  rw [hrel g]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  rw [← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]

theorem jumps_not_nodup' (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hτ : InducesW D.nd i τ w)
    (hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i))
    {a d u : ℕ} (h : d + d + u = a) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) (Qbar (D.nd.l i)))
    (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) (Qbar (D.nd.l i))) (Pm : GL (Fin a) (Qbar (D.nd.l i)))
    (hd : 0 < d) (hc : SumRepresentations.At.ContQ D.nd i ρ) (hcσ : SumRepresentations.At.ContQ D.nd i σ) (hcυ : SumRepresentations.At.ContQ D.nd i υ)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) (Qbar (D.nd.l i))) :
            Matrix _ _ (Qbar (D.nd.l i))))
    (hdR : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w') :
    ¬ (D.naut.jumpsW i ρ τ).Nodup := by
  intro hnd
  subst h
  obtain ⟨-, -, hJC, hG⟩ := ht.2.2
  obtain ⟨-, hconj, hsum, -⟩ := hG i
  have hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm := by
    intro g; ext1; rw [hrel g]; simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hcA := contQ_sumRep D i σ σ hcσ hcσ
  obtain ⟨hdRc, -, hJc⟩ := hconj _ ρ _ hc Pm hPm
  obtain ⟨hdRs, -, hJs⟩ := hsum _ _ _ υ hcA hcυ
  obtain ⟨hdRσ, -, hJσ⟩ := hsum _ _ σ σ hcσ hcσ
  have hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w' :=
    fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')
  have hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w' :=
    fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')
  have hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w' :=
    fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1
  have e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ := by
    rw [← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']
  have hcard := hJC i _ σ w τ hw hτ (hdRσ' w hτ).1
  rw [e] at hnd
  have h2 := (Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2
  obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)
  exact Multiset.disjoint_left.1 h2 hj hj

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem continuous_blocks' {k Γ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Group Γ]
    [TopologicalSpace Γ] {a b c : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ₁ : Γ →* GL (Fin b) k)
    (ρ₂ : Γ →* GL (Fin c) k) (h : b + c = a) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) :
    (Continuous fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) ∧
      Continuous fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k) := by
  subst h
  have hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) := by
    have e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g =>
        ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k) := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, hrel g]
      simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  constructor
  · have e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _
  · have e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

end GlobalTheory.AbsIrrConstituents
