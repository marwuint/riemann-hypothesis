import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

end

end GlobalTheory.KFinDual
