import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Indep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_add_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y z : C) :
    ip x ((y : A) + z) = ip x y + ip x z := by
  have h1 := hp.herm (y + z) x
  have h2 := hp.herm y x
  have h3 := hp.herm z x
  have h4 := hp.add y z x
  simp only [Submodule.coe_add] at h1 h4
  rw [← h1, ← h2, ← h3, h4, map_add]

theorem hp_zero_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) : ip x (0 : A) = 0 := by
  have h := hp_add_right hp x 0 0
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  linear_combination -h

theorem hp_sum_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) {ι : Type}
    (s : Finset ι) (w : ι → C) : ip x (∑ i ∈ s, (w i : A)) = ∑ i ∈ s, ip x (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hp_zero_right hp x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := hp_add_right hp x (w a) (∑ i ∈ s, w i)
    rw [Submodule.coe_sum] at h
    exact h

end Indep

section F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostF (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {n : ℕ}

theorem isotIn_le_of_intw {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (T : π'.S →ₗ[ℂ] π.S) (hT : Intw π' π T)
    (hsurj : LinearMap.range T = ⊤) : isotIn ρ C π ≤ isotIn ρ C π' := by
  unfold isotIn
  refine iSup₂_le fun Φ hΦ => ?_
  have hr : LinearMap.range (Φ.comp T) = LinearMap.range Φ := by
    rw [LinearMap.range_comp, hsurj, Submodule.map_top]
  rw [← hr]
  refine le_iSup₂ (f := fun (Ψ : π'.S →ₗ[ℂ] A) (_ : IsEqvA ρ π' Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ)
    (Φ.comp T) ⟨?_, hr ▸ hΦ.2⟩
  intro h f
  simp only [LinearMap.comp_apply]
  rw [hT h f]
  exact hΦ.1 h (T f)

theorem isotIn_iso {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') : isotIn ρ C π = isotIn ρ C π' := by
  unfold Formalism.L2.NG.FinTyp.Iso Formalism.L2.NG.IsoRep at h
  obtain ⟨T, hT⟩ := h
  apply le_antisymm
  · refine isotIn_le_of_intw ρ C (T.symm : π'.S →ₗ[ℂ] π.S) ?_ (LinearMap.range_eq_top.2 T.symm.surjective)
    intro h f
    have key : T ⟨_, π.stable h _ (T.symm f).2⟩ = ⟨_, π'.stable h _ f.2⟩ := by
      apply Subtype.ext
      rw [hT h (T.symm f) ⟨_, π.stable h _ (T.symm f).2⟩ rfl, LinearEquiv.apply_symm_apply]
    exact T.symm_apply_eq.2 key.symm
  · refine isotIn_le_of_intw ρ C (T : π.S →ₗ[ℂ] π'.S) ?_ (LinearMap.range_eq_top.2 T.surjective)
    intro h f
    apply Subtype.ext
    exact hT h f ⟨_, π.stable h _ f.2⟩ rfl

variable {Y W : Formalism.BasicNotions.TH.HSp D} {SpY SpW : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem isotL_iso (P : RowPsi W n) (M : Mult.DSModel W SpW) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (e : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') :
    isotL θ P M J χ e π = isotL θ P M J χ e π' := by
  unfold isotL
  rw [isotIn_iso (actM P M) (Minf θ P M) h]

end F

end Formalism.IndefR.principalLevelFrame
