import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.KudlaSiegelWeil

namespace GlobalTheory.SmallThetaModules

section Restricted

variable {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def AdmFun (s : ∀ i, N i) : Type := {l : ∀ i, N i →ₗ[ℂ] ℂ // {i | l i (s i) ≠ 1}.Finite}

def evFam (s : ∀ i, N i) (ξ : ∀ i, N i) : AdmFun s → ℂ := fun l => ∏ᶠ i, l.1 i (ξ i)

def RTens (s : ∀ i, N i) : Submodule ℂ (AdmFun s → ℂ) :=
  Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = evFam s ξ}

open Classical in

def pureT (s : ∀ i, N i) (ξ : ∀ i, N i) : RTens s :=
  if h : Restr s ξ then ⟨evFam s ξ, Submodule.subset_span ⟨ξ, h, rfl⟩⟩ else 0

theorem coe_pureT {s ξ : ∀ i, N i} (h : Restr s ξ) : (pureT s ξ : AdmFun s → ℂ) = evFam s ξ := by
  unfold pureT; rw [dif_pos h]

omit [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] in
theorem restr_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (x : N v) :
    Restr s (Function.update ξ v x) := by
  refine (h.insert v).subset fun i hi => ?_
  by_cases hv : i = v
  · exact Or.inl hv
  · right
    simpa [Function.update_of_ne hv] using hi

theorem mulSupport_fin {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) :
    (Function.mulSupport fun i => l.1 i (ξ i)).Finite := by
  refine (Set.Finite.union h l.2).subset fun i hi => ?_
  by_cases e : ξ i = s i
  · right
    simpa [e] using hi
  · exact Or.inl e

theorem evFam_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) (v : ι) (x : N v) :
    evFam s (Function.update ξ v x) l = l.1 v x * ∏ᶠ (i) (_ : i ≠ v), l.1 i (ξ i) := by
  unfold evFam
  rw [← mul_finprod_cond_ne v (mulSupport_fin (restr_update h v x) l), Function.update_self]
  congr 1
  refine finprod_congr fun i => finprod_congr fun hi => ?_
  rw [Function.update_of_ne hi]

theorem pureT_mlin [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (c : ℂ) (x y : N v) :
    pureT s (Function.update ξ v (c • x + y)) =
      c • pureT s (Function.update ξ v x) + pureT s (Function.update ξ v y) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, coe_pureT (restr_update h v _), coe_pureT (restr_update h v _),
    coe_pureT (restr_update h v _)]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, evFam_update h, map_add, map_smul, smul_eq_mul]
  ring

theorem pureT_span (s : ∀ i, N i) :
    Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = pureT s ξ} = ⊤ := by
  apply Submodule.map_injective_of_injective (RTens s).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  change _ = Submodule.span ℂ _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨ξ, h, rfl⟩, rfl⟩
    exact ⟨ξ, h, coe_pureT h⟩
  · rintro ⟨ξ, h, rfl⟩
    exact ⟨_, ⟨ξ, h, rfl⟩, coe_pureT h⟩

theorem pureT_sep (s : ∀ i, N i) (l : ∀ i, N i →ₗ[ℂ] ℂ) (hl : {i | l i (s i) ≠ 1}.Finite) :
    ∃ Λ : RTens s →ₗ[ℂ] ℂ, ∀ ξ, Restr s ξ → Λ (pureT s ξ) = ∏ᶠ i, l i (ξ i) :=
  ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : AdmFun s => ℂ) (show AdmFun s from ⟨l, hl⟩)).comp (RTens s).subtype,
    fun _ h => congrFun (coe_pureT h) (show AdmFun s from ⟨l, hl⟩)⟩

theorem exists_lift {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (m : ∀ i, M i)
    {S : Type} [AddCommGroup S] [Module ℂ S] (pu : (∀ i, M i) → S)
    (hsep : ∀ l : ∀ i, M i →ₗ[ℂ] ℂ, {i | l i (m i) ≠ 1}.Finite →
      ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l i (φ i))
    (s : ∀ i, N i) (p : ∀ i, M i →ₗ[ℂ] N i) :
    ∃ P : S →ₗ[ℂ] RTens s, ∀ φ, Restr m φ → P (pu φ) = pureT s fun i => p i (φ i) := by
  by_cases hp : {i | p i (m i) ≠ s i}.Finite
  · have h1 : ∀ l : AdmFun s, ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l.1 i (p i (φ i)) := by
      intro l
      refine hsep (fun i => (l.1 i).comp (p i)) ((hp.union l.2).subset fun i hi => ?_)
      by_cases e : p i (m i) = s i
      · right
        simpa [e] using hi
      · exact Or.inl e
    choose Λ hΛ using h1
    obtain ⟨r, hr⟩ := (RTens s).subtype.exists_leftInverse_of_injective (RTens s).ker_subtype
    refine ⟨r.comp (LinearMap.pi Λ), fun φ hφ => ?_⟩
    have h2 : Restr s fun i => p i (φ i) := by
      refine (Set.Finite.union hφ hp).subset fun i hi => ?_
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    have h3 : LinearMap.pi Λ (pu φ) = (RTens s).subtype (pureT s fun i => p i (φ i)) := by
      rw [Submodule.subtype_apply, coe_pureT h2]
      funext l
      exact hΛ l φ hφ
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  · refine ⟨0, fun φ hφ => ?_⟩
    have h2 : ¬ Restr s fun i => p i (φ i) := by
      intro h
      refine hp ((Set.Finite.union hφ h).subset fun i hi => ?_)
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    unfold pureT
    rw [dif_neg h2, LinearMap.zero_apply]

end Restricted

variable {D : D7} {X : ThetaX D}

section Collapse

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def colMon (V : HS D) : Pl D → Type
  | Sum.inl v => Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D))
  | Sum.inr _ => PUnit

instance (V : HS D) : ∀ v, Monoid (colMon V v)
  | Sum.inl v => inferInstanceAs (Monoid (Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D))))
  | Sum.inr _ => inferInstanceAs (Monoid PUnit)

end Collapse

end GlobalTheory.SmallThetaModules

end
