import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameRecord

section Transport

variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp (ρ : Representation ℂ H V) (φ : G →* H) (hφ : Continuous φ) (h : GlobalTheory.PRep.IsSmooth ρ) :
    GlobalTheory.PRep.IsSmooth (ρ.comp φ) := fun v => (h v).preimage hφ

theorem isIrreducible_comp (ρ : Representation ℂ H V) (φ : G →* H) (hs : Function.Surjective φ)
    (h : GlobalTheory.GLp.IsIrrRep ρ) : Representation.IsIrreducible (ρ.comp φ) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff]
  refine ⟨h.1, fun W hW => h.2 W fun y v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hW x v hv

theorem isSupercuspidal_comp [IsTopologicalGroup G] [IsTopologicalGroup H] (ρ : Representation ℂ H V) (φ : G →* H)
    (ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ) (h1 : ∀ x, ψ (φ x) = x) (h2 : ∀ y, φ (ψ y) = y)
    (h : GlobalTheory.PRep.IsSupercuspidal ρ) : GlobalTheory.PRep.IsSupercuspidal (ρ.comp φ) := by
  refine ⟨isSmooth_comp ρ φ hφ h.1, fun v l hl => ?_⟩
  have hl' : l ∈ GlobalTheory.PRep.smoothPart (Representation.dual ρ) := by
    have e : {y : H | Representation.dual ρ y l = l} =
        ψ ⁻¹' {x : G | Representation.dual (ρ.comp φ) x l = l} := by
      ext y
      simp [Representation.dual_apply, h2]
    show IsOpen {y : H | Representation.dual ρ y l = l}
    rw [e]
    exact hl.preimage hψ
  obtain ⟨C, hC, hCv⟩ := h.2 v l hl'
  refine ⟨ψ '' C, hC.image hψ, fun x hx => ?_⟩
  obtain ⟨z, hz, c, hc, e⟩ := hCv (φ x) hx
  refine ⟨ψ z, Subgroup.mem_center_iff.2 fun y => ?_, ψ c, ⟨c, hc, rfl⟩, ?_⟩
  · rw [← h1 y, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz (φ y))]
  · rw [← map_mul, ← e, h1]

end Transport

section GLMap

variable {n : Type} [Fintype n] [DecidableEq n] {K₁ K₂ : Type} [Field K₁] [Field K₂] [TopologicalSpace K₁]
  [TopologicalSpace K₂] [IsTopologicalRing K₁] [IsTopologicalRing K₂]

theorem continuous_glMap (f : K₁ →+* K₂) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

theorem glMap_symm_apply (i : K₁ ≃+* K₂) (x : GL n K₁) :
    Matrix.GeneralLinearGroup.map i.symm.toRingHom (Matrix.GeneralLinearGroup.map i.toRingHom x) = x := by
  ext a b
  simp

theorem glMap_apply_symm (i : K₁ ≃+* K₂) (y : GL n K₂) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom y) = y := by
  ext a b
  simp

end GLMap

theorem continuous_symm {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

def transRep {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨_, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    isSmooth_comp _ _ (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) hs,
    isIrreducible_comp _ _ (fun y => ⟨_, glMap_apply_symm (I.i k v).symm y⟩) h⟩

theorem transRep_comp {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    (transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom) = π.ρ :=
  MonoidHom.ext fun x => by
    show π.ρ _ = π.ρ x
    rw [glMap_symm_apply]

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    Nonempty (π ≅ pull I k v (transRep I k v π h hs)) :=
  by
    have E : π.ρ.Equiv ((transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) := by
      rw [transRep_comp]; exact Representation.Equiv.refl _
    exact ⟨(Rep.mkIso E : Rep.of π.ρ ≅ _)⟩

end GlobalTheory.TameRecord
